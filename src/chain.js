const CryptoJS = require('crypto-js')
const { randomBytes } = require('crypto')
const secp256k1 = require('secp256k1')
const bs58 = require('base-x')(config.b58Alphabet)
const series = require('run-series')
const cloneDeep = require('clone-deep')
const dao = require('./dao')
const daoMaster = require('./daoMaster')
const transaction = require('./transaction.js')
const notifications = require('./notifications.js')
const txHistory = require('./txHistory')
const blocks = require('./blocks')
const steem = require('./steem')
const GrowInt = require('growint')
const default_replay_output = 100
const replay_output = process.env.REPLAY_OUTPUT || default_replay_output
const max_batch_blocks = 10000

class Block {
    constructor(index, steemBlock, phash, timestamp, txs, miner, missedBy, dist, burn, signature, hash) {
        this._id = index
        this.steemblock = steemBlock
        this.phash = phash.toString()
        this.timestamp = timestamp
        this.txs = txs
        this.miner = miner
        if (missedBy) this.missedBy = missedBy
        if (dist) this.dist = dist
        if (burn) this.burn = burn
        this.hash = hash
        this.signature = signature
        
        // Set syncMode if we're behind OR in transition period
        if (steem && steem.getBehindBlocks) {
            const behindBlocks = steem.getBehindBlocks()
            // Stay in sync mode if significantly behind or recently caught up
            if (behindBlocks > 5 || (steem.lastSyncExitTime && new Date().getTime() - steem.lastSyncExitTime < 10000)) {
                this.syncMode = true
            }
        }
    }
}

let chain = {
    blocksToRebuild: [],
    restoredBlocks: 0,
    schedule: null,
    recentBlocks: [],
    recentTxs: {},
    shuttingDown: false,
    recovering: false,
    recoveryAttempts: {},
    recoveryFailCount: 0,
    maxRecoveryAttempts: 3,
    lastValidationError: null,
    getNewKeyPair: () => {
        let privKey, pubKey
        do {
            privKey = randomBytes(config.randomBytesLength)
            pubKey = secp256k1.publicKeyCreate(privKey)
        } while (!secp256k1.privateKeyVerify(privKey))

        return {
            pub: bs58.encode(pubKey),
            priv: bs58.encode(privKey)
        }
    },
    getGenesisBlock: () => {
        return new Block(
            0,
            config.steemStartBlock,
            '0',
            0,
            [],
            config.masterName,
            null,
            null,
            null,
            '0000000000000000000000000000000000000000000000000000000000000000',
            config.originHash
        )
    },
    prepareBlock: (cb) => {
        let previousBlock = chain.getLatestBlock()
        let nextIndex = previousBlock._id + 1
        
        // Calculate the appropriate timestamp based on miner priority
        let minerPriority = 1 // Default priority for the leader
        if (chain.schedule.shuffle[(nextIndex - 1) % config.leaders].name !== process.env.NODE_OWNER) {
            // We're not the scheduled leader, calculate our priority
            for (let i = 1; i < 2 * config.leaders; i++) {
                if (chain.recentBlocks[chain.recentBlocks.length - i]
                    && chain.recentBlocks[chain.recentBlocks.length - i].miner === process.env.NODE_OWNER) {
                    minerPriority = i + 1
                    break
                }
            }
        }
        
        // Calculate timestamp with proper padding to ensure it passes validation
        const blockTime = (steem.isSyncing() || (steem.lastSyncExitTime && new Date().getTime() - steem.lastSyncExitTime < 10000))
            ? config.syncBlockTime 
            : config.blockTime
        const minimumTimestamp = previousBlock.timestamp + (minerPriority * blockTime)
        
        // Add a small buffer to ensure the block is not too early for other nodes
        // Use a larger buffer during sync mode to accommodate faster block production
        const maxDriftValue = (steem.isSyncing() || (steem.lastSyncExitTime && new Date().getTime() - steem.lastSyncExitTime < 10000))
            ? config.syncMaxDrift 
            : config.maxDrift
        const bufferTime = (steem.isSyncing() || (steem.lastSyncExitTime && new Date().getTime() - steem.lastSyncExitTime < 10000)) 
            ? (nextIndex <= 10 ? 80 : 50)  // Larger buffer in sync mode
            : (nextIndex <= 10 ? 50 : 25)  // Standard buffer in normal mode
        
        const nextTimestamp = Math.max(
            new Date().getTime() + bufferTime,  // Current time plus buffer
            minimumTimestamp + bufferTime       // Minimum time plus buffer
        )
        
        logr.debug(`Preparing block with timestamp ${nextTimestamp}, min: ${minimumTimestamp}, priority: ${minerPriority}`)
        
        let nextSteemBlock = previousBlock.steemblock + 1
        
        // Process Steem block first to get its transactions in the mempool
        steem.processBlock(nextSteemBlock).then((transactions) => {
            if (!transactions) {
                logr.warn(`Cannot prepare block - Steem block ${nextSteemBlock} not found`)
                cb(true, null)
                return
            }
            
            // Add mempool transactions
            let txs = []
            let mempool = transaction.pool.sort(function (a, b) { return a.ts - b.ts })

            loopOne:
            for (let i = 0; i < mempool.length; i++) {
                if (txs.length === config.maxTxPerBlock)
                    break
                // do not allow multiple txs from same account in the same block
                for (let y = 0; y < txs.length; y++)
                    if (txs[y].sender === mempool[i].sender)
                        continue loopOne
                txs.push(mempool[i])
            }

            loopTwo:
            for (let i = 0; i < mempool.length; i++) {
                if (txs.length === config.maxTxPerBlock)
                    break
                for (let y = 0; y < txs.length; y++)
                    if (txs[y].hash === mempool[i].hash)
                        continue loopTwo
                txs.push(mempool[i])
            }
            txs = txs.sort(function (a, b) { return a.ts - b.ts })

            transaction.removeFromPool(txs)
            
            // Create the initial block
            let newBlock = new Block(nextIndex, nextSteemBlock, previousBlock.hash, nextTimestamp, txs, process.env.NODE_OWNER)
            
            // Set distribution amount based on leader rewards
            if (config.leaderReward > 0) {
                newBlock.dist = config.leaderReward
            }
            
            // hash and sign the block with our private key
            newBlock = chain.hashAndSignBlock(newBlock)
            cb(null, newBlock)
            return
        }).catch((error) => {
            logr.error(`Error processing Steem block ${nextSteemBlock}:`, error)
            cb(true, null)
            return
        })
    },
    hashAndSignBlock: (block) => {
        let nextHash = chain.calculateHashForBlock(block)
        let signature = secp256k1.ecdsaSign(Buffer.from(nextHash, 'hex'), bs58.decode(process.env.NODE_OWNER_PRIV))
        signature = bs58.encode(signature.signature)
        return new Block(block._id, block.steemblock, block.phash, block.timestamp, block.txs, block.miner, block.missedBy, block.dist, block.burn, signature, nextHash)
    },
    canMineBlock: (cb) => {
        if (chain.shuttingDown) {
            cb(true, null); return
        }
        chain.prepareBlock(function (err, newBlock) {
            // run the transactions and validation
            // pre-validate our own block (not the hash and signature as we dont have them yet)
            // nor transactions because we will filter them on execution later
            chain.isValidNewBlock(newBlock, false, false, function (isValid) {
                if (!isValid) {
                    cb(true, newBlock); return
                }
                cb(null, newBlock)
            })
        })

    },
    mineBlock: (cb) => {
        if (chain.shuttingDown) {
            cb('Node is shutting down', null)
            return
        }

        chain.canMineBlock(function (err, newBlock) {
            if (err) {
                cb(true, newBlock); return
            }
            // at this point transactions in the pool seem all validated
            // BUT with a different ts and without checking for double spend
            // so we will execute transactions in order and revalidate after each execution
            chain.executeBlockTransactions(newBlock, true, function (validTxs, distributed, burned) {
                try {
                    cache.rollback()
                    dao.resetID()
                    daoMaster.resetID()
                    // and only add the valid txs to the new block
                    newBlock.txs = validTxs

                    // always record the failure of others
                    if (chain.schedule.shuffle[(newBlock._id - 1) % config.leaders].name !== process.env.NODE_OWNER)
                        newBlock.missedBy = chain.schedule.shuffle[(newBlock._id - 1) % config.leaders].name

                    if (distributed) newBlock.dist = distributed
                    if (burned) newBlock.burn = burned

                    // hash and sign the block with our private key
                    newBlock = chain.hashAndSignBlock(newBlock)

                    // push the new block to consensus possible blocks
                    // and go straight to end of round 0 to skip re-validating the block
                    let possBlock = {
                        block: newBlock
                    }
                    for (let r = 0; r < config.consensusRounds; r++)
                        possBlock[r] = []

                    logr.debug('Mined a new block, proposing to consensus')

                    possBlock[0].push(process.env.NODE_OWNER)
                    consensus.possBlocks.push(possBlock)
                    consensus.endRound(0, newBlock)
                    cb(null, newBlock)
                } catch (error) {
                    logr.error('Error while finalizing block:', error)
                    cb(error, null)
                }
            })
        })
    },
    validateAndAddBlock: (newBlock, cb, noSync) => {
        // Check for null or undefined block
        if (!newBlock) {
            logr.error('Cannot validate and add null or undefined block')
            if (cb) cb(false)
            return
        }

        // Validate required block properties
        if (!newBlock._id || typeof newBlock._id !== 'number') {
            logr.error('Invalid block index in validateAndAddBlock')
            if (cb) cb(false)
            return
        }

        // Validate the block
        chain.isValidNewBlock(newBlock, (isValid) => {
            if (!isValid) {
                // If we're in sync mode and the error is an invalid phash, handle it differently
                if (chain.lastValidationError === 'invalid phash' && (steem.isSyncing() || p2p.recovering)) {
                    if (newBlock && newBlock.miner && !chain.recoveryAttempts[newBlock.miner]) 
                        chain.recoveryAttempts[newBlock.miner] = 0
                    
                    // Increment recovery attempts for this miner
                    chain.recoveryAttempts[newBlock.miner]++
                    
                    // Log information about the invalid phash for debugging
                    const latestBlock = chain.getLatestBlock()
                    logr.warn(`Invalid phash during sync mode for block #${newBlock._id} by ${newBlock.miner} - this is normal during fast sync`)
                    logr.warn(`Latest block #${latestBlock._id} has hash ${latestBlock.hash} but new block has phash ${newBlock.phash}`)
                    
                    // Progressive recovery strategy
                    if (chain.recoveryAttempts[newBlock.miner] <= 3) {
                        // First attempts: go back a few blocks for better fork detection
                        const blocksToGoBack = Math.min(3 * chain.recoveryAttempts[newBlock.miner], 15)
                        const targetBlock = Math.max(latestBlock._id - blocksToGoBack, 1)
                        logr.warn(`Invalid phash detected during sync mode (attempt #${chain.recoveryAttempts[newBlock.miner]}), trying targeted recovery`)
                        logr.info(`Sync mode recovery: going back ${blocksToGoBack} blocks to ${targetBlock} for better fork detection`)
                        
                        // Trigger recovery from the specific block
                        p2p.recovering = true
                        chain.recovering = true
                        chain.recoveryTargetBlock = targetBlock
                        
                        // Request block recovery from peers
                        p2p.recoverBlock(targetBlock, (err, block) => {
                            if (err || !block) {
                                logr.error(`Recovery failed for block ${targetBlock}:`, err || 'No block returned')
                                chain.recoveryFailCount = (chain.recoveryFailCount || 0) + 1
                            } else {
                                logr.info(`Recovered block #${targetBlock} successfully`)
                                chain.recoveryFailCount = 0
                            }
                            
                            // Exit recovery after a short timeout
                            setTimeout(() => {
                                p2p.recovering = false
                                chain.recovering = false
                            }, 1000)
                        })
                    } else if (chain.recoveryAttempts[newBlock.miner] <= 5) {
                        // More aggressive recovery: try to find common ancestor
                        logr.warn(`Repeated invalid phash from ${newBlock.miner}, attempting more aggressive recovery`)
                        
                        // Find a block further back to attempt recovery from
                        const blocksToGoBack = 20 + (10 * (chain.recoveryAttempts[newBlock.miner] - 3))
                        const targetBlock = Math.max(latestBlock._id - blocksToGoBack, 1)
                        logr.info(`Deep sync recovery: going back ${blocksToGoBack} blocks to ${targetBlock}`)
                        
                        // Trigger deep recovery
                        p2p.recovering = true
                        chain.recovering = true
                        chain.recoveryTargetBlock = targetBlock
                        
                        p2p.recoverBlock(targetBlock, (err, block) => {
                            if (err || !block) {
                                logr.error(`Deep recovery failed for block ${targetBlock}:`, err || 'No block returned')
                                chain.recoveryFailCount = (chain.recoveryFailCount || 0) + 1
                            } else {
                                logr.info(`Deep recovery successful from block #${targetBlock}`)
                                chain.recoveryFailCount = 0
                            }
                            
                            setTimeout(() => {
                                p2p.recovering = false
                                chain.recovering = false
                            }, 2000)
                        })
                    } else {
                        // If too many attempts, try a different approach or skip
                        logr.error(`Too many recovery attempts (${chain.recoveryAttempts[newBlock.miner]}) for miner ${newBlock.miner}, trying different approach`)
                        
                        // If we've tried many approaches and failed, try requesting head blocks from peers
                        if (chain.recoveryFailCount > 10) {
                            logr.error(`Recovery failing consistently, requesting network head blocks`)
                            p2p.broadcastHeadBlockRequest()
                            
                            // Reset recovery attempts after extensive failures to try again with basic strategy
                            chain.recoveryAttempts = {}
                            chain.recoveryFailCount = 0
                            
                            // Force a longer timeout to let network stabilize
                            setTimeout(() => {
                                if (p2p.recovering) {
                                    logr.info('Exiting recovery mode after timeout')
                                    p2p.recovering = false
                                    chain.recovering = false
                                }
                            }, 10000)
                        } else {
                            // Reset recovery after too many attempts from this miner
                            setTimeout(() => {
                                chain.recoveryAttempts[newBlock.miner] = 0
                                p2p.recovering = false
                                chain.recovering = false
                            }, 5000)
                        }
                    }
                }
                
                cb(false)
                return
            }

            // Block is valid, try to add it
            let revalidate = false
            // ... existing code ...
        })
    },
    executeValidatedBlock: (newBlock, revalidate, cb) => {
        // straight execution
        chain.executeBlockTransactions(newBlock, revalidate, function (validTxs, distributed, burned) {
            // if any transaction is wrong, thats a fatal error
            if (newBlock.txs.length !== validTxs.length) {
                logr.error('Invalid tx(s) in block')
                cb(true, newBlock); return
            }

            // error if distributed or burned computed amounts are different than the reported one
            let blockDist = newBlock.dist || 0
            if (blockDist !== distributed) {
                logr.error('Wrong dist amount', blockDist, distributed)
                cb(true, newBlock); return
            }
            let blockBurn = newBlock.burn || 0
            if (blockBurn !== burned) {
                logr.error('Wrong burn amount', blockBurn, burned)
                cb(true, newBlock); return
            }

            // add txs to recents
            chain.addRecentTxsInBlock(newBlock.txs)

            // remove all transactions from this block from our transaction pool
            transaction.removeFromPool(newBlock.txs)

            chain.addBlock(newBlock, function () {
                // and broadcast to peers (if not replaying)
                if (!p2p.recovering)
                    p2p.broadcastBlock(newBlock)

                // process notifications and leader stats (non blocking)
                notifications.processBlock(newBlock)

                // emit event to confirm new transactions in the http api
                if (!p2p.recovering)
                    for (let i = 0; i < newBlock.txs.length; i++)
                        transaction.eventConfirmation.emit(newBlock.txs[i].hash)

                cb(null, newBlock)
            })
        })
    },
    addRecentTxsInBlock: (txs = []) => {
        for (let t in txs)
            chain.recentTxs[txs[t].hash] = txs[t]
    },
    minerWorker: (block) => {
        if (p2p.recovering) return
        clearTimeout(chain.worker)

        if (chain.schedule.shuffle.length === 0) {
            logr.fatal('All leaders gave up their stake? Chain is over')
            process.exit(1)
        }

        let mineInMs = null
        // Get the appropriate block time based on sync state
        let blockTime = (steem.isSyncing() || (steem.lastSyncExitTime && new Date().getTime() - steem.lastSyncExitTime < 10000))
            ? config.syncBlockTime 
            : config.blockTime

        // if we are the next scheduled witness, try to mine in time
        if (chain.schedule.shuffle[(block._id) % config.leaders].name === process.env.NODE_OWNER)
            mineInMs = blockTime
        // else if the scheduled leaders miss blocks
        // backups witnesses are available after each block time intervals
        else for (let i = 1; i < 2 * config.leaders; i++)
            if (chain.recentBlocks[chain.recentBlocks.length - i]
                && chain.recentBlocks[chain.recentBlocks.length - i].miner === process.env.NODE_OWNER) {
                mineInMs = (i + 1) * blockTime
                break
            }

        if (mineInMs) {
            mineInMs -= (new Date().getTime() - block.timestamp)
            mineInMs += 20
            logr.debug('Trying to mine in ' + mineInMs + 'ms' + ' (sync: ' + steem.isSyncing() + ')')
            consensus.observer = false
            
            // More lenient performance check during sync mode
            if (steem.isSyncing()) {
                // During sync, only skip if extremely slow (less than 10% of block time)
                if (mineInMs < blockTime / 10) {
                    logr.warn('Extremely slow performance during sync, skipping block')
                    return
                }
            } else {
                // Normal mode - use standard performance check
                if (mineInMs < blockTime / 3) {
                    logr.warn('Slow performance detected, will not try to mine next block')
                    return
                }
            }
            
            // Make sure the node is marked as ready to receive transactions now that we're mining
            if (steem && steem.setReadyToReceiveTransactions)
                steem.setReadyToReceiveTransactions(true)
                
            chain.worker = setTimeout(function () {
                chain.mineBlock(function (error, finalBlock) {
                    if (error)
                        logr.warn('miner worker trying to mine but couldnt', finalBlock)
                })
            }, mineInMs)
        }

    },
    addBlock: async (block, cb) => {
        // add the block in our own db
        if (blocks.isOpen)
            blocks.appendBlock(block)
        else
            await db.collection('blocks').insertOne(block)

        // push cached accounts and contents to mongodb
        chain.cleanMemory()

        // update the config if an update was scheduled
        config = require('./config.js').read(block._id)
        eco.appendHistory(block)
        eco.nextBlock()
        dao.nextBlock()
        daoMaster.nextBlock()
        leaderStats.processBlock(block)
        txHistory.processBlock(block)

        // Check if we should exit sync mode - only when fully caught up
        if (steem && steem.isSyncing && steem.isSyncing() && 
            steem.getBehindBlocks() === 0) {
            steem.exitSyncMode()
            logr.info('Exiting sync mode - chain fully caught up')
        }

        // if block id is mult of n leaders, reschedule next n blocks
        if (block._id % config.leaders === 0)
            chain.schedule = chain.minerSchedule(block)
        chain.recentBlocks.push(block)
        chain.minerWorker(block)
        chain.output(block)
        cache.writeToDisk(false)
        cb(true)
    },
    output: (block, rebuilding) => {
        chain.nextOutput.txs += block.txs.length
        if (block.dist)
            chain.nextOutput.dist += block.dist
        if (block.burn)
            chain.nextOutput.burn += block.burn

        if (block._id % replay_output === 0 || (!rebuilding && !p2p.recovering)) {
            let currentOutTime = new Date().getTime()
            let output = ''
            if (rebuilding)
                output += 'Rebuilt '

            output += '#' + block._id

            if (rebuilding)
                output += '/' + chain.restoredBlocks
            else
                output += '  by ' + block.miner

            output += '  ' + chain.nextOutput.txs + ' tx'
            if (chain.nextOutput.txs > 1)
                output += 's'

            output += '  dist: ' + eco.round(chain.nextOutput.dist)
            output += '  burn: ' + eco.round(chain.nextOutput.burn)
            output += '  delay: ' + (currentOutTime - block.timestamp)
            output += '  steem block: ' + block.steemblock
            
            // Add sync status information with more detail
            if (steem && steem.isSyncing && steem.getBehindBlocks) {
                const behind = steem.getBehindBlocks()
                const isSyncing = steem.isSyncing()
                
                if (behind > 0 || isSyncing) {
                    output += '  sync: ' + (isSyncing ? 'YES' : 'NO')
                    if (behind > 0) {
                        output += ' (' + behind + ' blocks behind)'
                        
                        // Add estimated time to completion
                        const processingRate = 1;  // blocks per second
                        const steemProductionRate = 1/3;  // blocks per second
                        const netCatchupRate = processingRate - steemProductionRate;
                        
                        if (netCatchupRate > 0) {
                            const secondsToSync = Math.ceil(behind / netCatchupRate);
                            const minutesToSync = Math.ceil(secondsToSync / 60);
                            
                            if (minutesToSync < 60) {
                                output += ' (~' + minutesToSync + ' min to sync)';
                            } else {
                                const hoursToSync = Math.floor(minutesToSync / 60);
                                const remainingMinutes = minutesToSync % 60;
                                output += ' (~' + hoursToSync + 'h ' + remainingMinutes + 'm to sync)';
                            }
                        }
                    }
                }
            }

            // Add catching up message only when behind in sidechain blocks
            if (!rebuilding && !p2p.recovering && consensus && consensus.observer) {
                const latestBlock = chain.getLatestBlock()
                const latestBlockId = latestBlock ? latestBlock._id : 0
                
                // Get network height from consensus possible blocks
                let networkHeight = latestBlockId
                if (consensus.possBlocks && consensus.possBlocks.length > 0) {
                    for (let possBlock of consensus.possBlocks) {
                        if (possBlock.block && possBlock.block._id > networkHeight) {
                            networkHeight = possBlock.block._id
                        }
                    }
                }
                
                // Also check consensus last block
                if (consensus.lastBlock && consensus.lastBlock._id > networkHeight) {
                    networkHeight = consensus.lastBlock._id
                }

                if (networkHeight > latestBlockId) {
                    const blocksBehind = networkHeight - latestBlockId
                    logr.info('Catching up with network, head block: ' + latestBlockId + 
                            ', behind: ' + blocksBehind + ' blocks')
                }
            }
            
            if (block.missedBy && !rebuilding)
                output += '  MISS: ' + block.missedBy
            else if (rebuilding) {
                output += '  Performance: ' + Math.floor(replay_output / (currentOutTime - chain.lastRebuildOutput) * 1000) + 'b/s'
                chain.lastRebuildOutput = currentOutTime
            }

            logr.info(output)
            chain.nextOutput = {
                txs: 0,
                dist: 0,
                burn: 0
            }
        }

    },
    nextOutput: {
        txs: 0,
        dist: 0,
        burn: 0
    },
    lastRebuildOutput: 0,
    isValidPubKey: (key) => {
        try {
            return secp256k1.publicKeyVerify(bs58.decode(key))
        } catch (error) {
            return false
        }
    },
    isValidSignature: (user, txType, hash, sign, cb) => {
        // verify signature and bandwidth
        cache.findOne('accounts', { name: user }, async function (err, account) {
            if (err) throw err
            if (!account) {
                cb(false); return
            } else if (chain.restoredBlocks && chain.getLatestBlock()._id < chain.restoredBlocks && process.env.REBUILD_NO_VERIFY === '1')
                // no verify rebuild mode, only use if you trust the contents of blocks.zip
                return cb(account)

            // main key can authorize all transactions
            let allowedPubKeys = [[account.pub, account.pub_weight || 1]]
            let threshold = 1
            // add all secondary keys having this transaction type as allowed keys
            if (account.keys && typeof txType === 'number' && Number.isInteger(txType))
                for (let i = 0; i < account.keys.length; i++)
                    if (account.keys[i].types.indexOf(txType) > -1)
                        allowedPubKeys.push([account.keys[i].pub, account.keys[i].weight || 1])
            // account authorities
            if (account.auths && typeof txType === 'number' && Number.isInteger(txType))
                for (let i in account.auths)
                    if (account.auths[i].types.indexOf(txType) > -1) {
                        let authorizedAcc = await cache.findOnePromise('accounts', { name: account.auths[i].user })
                        if (authorizedAcc && authorizedAcc.keys)
                            for (let a in authorizedAcc.keys)
                                if (authorizedAcc.keys[a].id === account.auths[i].id) {
                                    allowedPubKeys.push([authorizedAcc.keys[a].pub, account.auths[i].weight || 1])
                                    break
                                }
                    }

            // if there is no transaction type
            // it means we are verifying a block signature
            // so only the leader key is allowed
            if (txType === null)
                if (account.pub_leader)
                    allowedPubKeys = [[account.pub_leader, 1]]
                else
                    allowedPubKeys = []
            // compute required signature threshold otherwise
            else if (account.thresholds && account.thresholds[txType])
                threshold = account.thresholds[txType]
            else if (account.thresholds && account.thresholds.default)
                threshold = account.thresholds.default

            // multisig transactions
            if (config.multisig && Array.isArray(sign))
                return chain.isValidMultisig(account, threshold, allowedPubKeys, hash, sign, cb)

            // single signature
            try {
                for (let i = 0; i < allowedPubKeys.length; i++) {
                    let bufferHash = Buffer.from(hash, 'hex')
                    let b58sign = bs58.decode(sign)
                    let b58pub = bs58.decode(allowedPubKeys[i][0])
                    if (secp256k1.ecdsaVerify(b58sign, bufferHash, b58pub) && allowedPubKeys[i][1] >= threshold) {
                        cb(account)
                        return
                    }
                }
            } catch (e) { }
            cb(false)
        })
    },
    isValidMultisig: (account, threshold, allowedPubKeys, hash, signatures, cb) => {
        let validWeights = 0
        let validSigs = []
        try {
            let hashBuf = Buffer.from(hash, 'hex')
            for (let s = 0; s < signatures.length; s++) {
                let signBuf = bs58.decode(signatures[s][0])
                let recoveredPub = bs58.encode(secp256k1.ecdsaRecover(signBuf, signatures[s][1], hashBuf))
                if (validSigs.includes(recoveredPub))
                    return cb(false, 'duplicate signatures found')
                for (let p = 0; p < allowedPubKeys.length; p++)
                    if (allowedPubKeys[p][0] === recoveredPub) {
                        validWeights += allowedPubKeys[p][1]
                        validSigs.push(recoveredPub)
                    }
            }
        } catch (e) {
            return cb(false, 'invalid signatures: ' + e.toString())
        }
        if (validWeights >= threshold)
            cb(account)
        else
            cb(false, 'insufficient signature weight ' + validWeights + ' to reach threshold of ' + threshold)
    },
    isValidHashAndSignature: (newBlock, cb) => {
        // and that the hash is correct
        let theoreticalHash = chain.calculateHashForBlock(newBlock, true)
        if (theoreticalHash !== newBlock.hash) {
            logr.debug(typeof (newBlock.hash) + ' ' + typeof theoreticalHash)
            chain.lastValidationError = 'invalid hash'
            logr.error('invalid hash: ' + theoreticalHash + ' ' + newBlock.hash)
            cb(false); return
        }

        // finally, verify the signature of the miner
        chain.isValidSignature(newBlock.miner, null, newBlock.hash, newBlock.signature, function (legitUser) {
            if (!legitUser) {
                chain.lastValidationError = 'invalid miner signature'
                logr.error('invalid miner signature')
                cb(false); return
            }
            cb(true)
        })
    },
    isValidBlockTxs: (newBlock, cb) => {
        chain.executeBlockTransactions(newBlock, true, function (validTxs, dist, burn) {
            cache.rollback()
            dao.resetID()
            daoMaster.resetID()
            if (validTxs.length !== newBlock.txs.length) {
                chain.lastValidationError = 'invalid block transaction'
                logr.error('invalid block transaction')
                cb(false); return
            }
            let blockDist = newBlock.dist || 0
            if (blockDist !== dist) {
                chain.lastValidationError = 'wrong dist amount'
                logr.error('Wrong dist amount', blockDist, dist)
                return cb(false)
            }

            let blockBurn = newBlock.burn || 0
            if (blockBurn !== burn) {
                chain.lastValidationError = 'wrong burn amount'
                logr.error('Wrong burn amount', blockBurn, burn)
                return cb(false)
            }
            cb(true)
        })
    },
    isValidNewBlock: (newBlock, cb) => {
        // Add robust null/undefined check at the beginning
        if (!newBlock) {
            chain.lastValidationError = 'block is null or undefined'
            logr.error('Block validation failed: block is null or undefined')
            cb(false)
            return
        }

        // Check if hash is defined, calculate it if not
        if (!newBlock.hash) {
            try {
                newBlock.hash = chain.calculateHashForBlock(newBlock)
            } catch (err) {
                chain.lastValidationError = 'failed to calculate block hash'
                logr.error('Block validation failed: failed to calculate hash:', err)
                cb(false)
                return
            }
        }

        // If we're starting up, still validating old blocks, rebuilding or recovering, allow all blocks without signature validation
        if (!chain.getLatestBlock() || !chain.getLatestBlock().hash || p2p.recovering || chain.recovering) {
            chain.lastValidationError = null
            cb(true)
            return
        }
        
        // Check if we have the block already
        if (chain.blocksMap[newBlock.hash]) {
            chain.lastValidationError = 'duplicate'
            //logr.debug('duplicate block', newBlock._id)
            cb(false)
            return
        }
        
        // If there's a cached invalid block hash, check against it
        if (chain.invalidBlocks[newBlock.hash]) {
            chain.lastValidationError = 'known invalid'
            cb(false)
            return
        }
        
        // Check block in more detail
        
        if (chain.recentBlocks.length > chain.blockIdWindow && chain.recentBlocks.includes(newBlock._id)) {
            chain.lastValidationError = 'duplicate blockId'
            cb(false)
            return
        }

        const prevBlock = chain.getLatestBlock()
        // ... existing code ...

        // check if previous block hash matches previous hash of new block
        if (prevBlock.hash !== newBlock.phash) {
            chain.lastValidationError = 'invalid phash'
            logr.error('invalid phash')
            cb(false)
            return
        }
        // ... existing code ...
    },
    isValidNewBlockPromise: (newBlock, verifyHashAndSig, verifyTxValidity) => new Promise((rs) => chain.isValidNewBlock(newBlock, verifyHashAndSig, verifyTxValidity, rs)),
    executeBlockTransactions: (block, revalidate, cb) => {
        // revalidating transactions in orders if revalidate = true
        // adding transaction to recent transactions (to prevent tx re-use) if isFinal = true
        let executions = []

        // Get required accounts from transactions
        const accounts = new Set()
        for (let tx of block.txs) {
            // Add sender
            if (tx.sender) accounts.add(tx.sender)
            // Add recipient for token operations
            if (tx.data && tx.data.payload && tx.data.payload.to) {
                accounts.add(tx.data.payload.to)
            }
        }

        // Create missing accounts first
        executions.push(function (callback) {
            series(Array.from(accounts).map(accountName => {
                return function (accountCallback) {
                    cache.findOne('accounts', { name: accountName.toLowerCase() }, function (err, existingAccount) {
                        if (err) {
                            accountCallback(err)
                            return
                        }

                        if (!existingAccount) {
                            const account = {
                                name: accountName.toLowerCase(),
                                balance: 0,
                                tokens: {},
                                created: {
                                    ts: block.timestamp
                                },
                            }
                            cache.insertOne('accounts', account, function (err) {
                                if (err) {
                                    accountCallback(err)
                                    return
                                }
                                logr.info('Created account:', accountName)
                                accountCallback(null, { created: true })
                            })
                        } else {
                            accountCallback(null, { exists: true })
                        }
                    })
                }
            }), callback)
        })

        // Then process all transactions
        for (let i = 0; i < block.txs.length; i++) {
            executions.push(function (callback) {
                let tx = block.txs[i]
                if (revalidate)
                    transaction.isValid(tx, block.timestamp, function (isValid, error) {
                        if (isValid)
                            transaction.execute(tx, block.timestamp, function (executed, distributed, burned) {
                                if (!executed) {
                                    logr.fatal('Tx execution failure', tx)
                                    process.exit(1)
                                }
                                callback(null, {
                                    executed: executed,
                                    distributed: distributed,
                                    burned: burned
                                })
                            })
                        else {
                            logr.error(error, tx)
                            callback(null, { executed: false })
                        }
                    })
                else
                    transaction.execute(tx, block.timestamp, function (executed, distributed, burned) {
                        if (!executed)
                            logr.fatal('Tx execution failure', tx)
                        callback(null, {
                            executed: executed,
                            distributed: distributed,
                            burned: burned
                        })
                    })
            })
        }

        executions.push((callback) => chain.applyHardfork(block, callback))

        let blockTimeBefore = new Date().getTime()
        series(executions, function (err, results) {
            if (err) throw err

            // First result is from account creation
            const accountResults = results.shift()

            // Rest are from transaction execution
            let executedSuccesfully = []
            let distributedInBlock = 0
            let burnedInBlock = 0

            for (let i = 0; i < block.txs.length; i++) {
                const result = results[i]
                if (result && result.executed) {
                    executedSuccesfully.push(block.txs[i])
                    if (result.distributed) distributedInBlock += result.distributed
                    if (result.burned) burnedInBlock += result.burned
                }
            }

            let string = 'executed'
            if (revalidate) string = 'validated & ' + string
            logr.debug('Block ' + string + ' in ' + (new Date().getTime() - blockTimeBefore) + 'ms')

            // execute periodic burn
            chain.decayBurnAccount(block).then(additionalBurn => {
                burnedInBlock += additionalBurn

                // execute dao triggers
                dao.runTriggers(block.timestamp).then(daoBurn => {
                    burnedInBlock += daoBurn
                    burnedInBlock = Math.round(burnedInBlock * 1000) / 1000

                    // add rewards for the leader who mined this block
                    chain.leaderRewards(block.miner, block.timestamp, function (dist) {
                        distributedInBlock += dist
                        distributedInBlock = Math.round(distributedInBlock * 1000) / 1000
                        cb(executedSuccesfully, distributedInBlock, burnedInBlock)
                    })
                })
            })
        })
    },
    minerSchedule: (block) => {
        let hash = block.hash
        let rand = parseInt('0x' + hash.substr(hash.length - config.leaderShufflePrecision))
        if (!p2p.recovering)
            logr.debug('Generating schedule... NRNG: ' + rand)
        let miners = chain.generateLeaders(true, false, config.leaders, 0)
        miners = miners.sort(function (a, b) {
            if (a.name < b.name) return -1
            if (a.name > b.name) return 1
            return 0
        })
        let shuffledMiners = []
        while (miners.length > 0) {
            let i = rand % miners.length
            shuffledMiners.push(miners[i])
            miners.splice(i, 1)
        }

        let y = 0
        while (shuffledMiners.length < config.leaders) {
            shuffledMiners.push(shuffledMiners[y])
            y++
        }

        return {
            block: block,
            shuffle: shuffledMiners
        }
    },
    generateLeaders: (withLeaderPub, withWs, limit, start) => {
        let leaders = []
        let leaderAccs = withLeaderPub ? cache.leaders : cache.accounts
        for (const key in leaderAccs) {
            if (!cache.accounts[key].node_appr || cache.accounts[key].node_appr <= 0)
                continue
            if (withLeaderPub && !cache.accounts[key].pub_leader)
                continue
            let leader = cache.accounts[key]
            let leaderDetails = {
                name: leader.name,
                pub: leader.pub,
                pub_leader: leader.pub_leader,
                balance: leader.balance,
                approves: leader.approves,
                node_appr: leader.node_appr,
            }
            if (withWs && leader.json && leader.json.node && typeof leader.json.node.ws === 'string')
                leaderDetails.ws = leader.json.node.ws
            leaders.push(leaderDetails)
        }
        leaders = leaders.sort(function (a, b) {
            return b.node_appr - a.node_appr
        })
        return leaders.slice(start, limit)
    },
    leaderRewards: (name, ts, cb) => {
        // rewards leaders with 'free' voting power in the network
        cache.findOne('accounts', { name: name }, function (err, account) {
            let newBalance = account.balance + config.leaderReward

            if (config.leaderReward > 0 || config.leaderRewardVT > 0)
                cache.updateOne('accounts',
                    { name: account.name },
                    {
                        $set: {
                            balance: newBalance
                        }
                    },
                    function (err) {
                        if (err) throw err
                        if (config.leaderReward > 0)
                            transaction.adjustNodeAppr(account, config.leaderReward, function () {
                                cb(config.leaderReward)
                            })
                        else
                            cb(0)
                    }
                )
            else cb(0)
        }, true)
    },
    decayBurnAccount: (block) => {
        return new Promise((rs) => {
            if (!config.burnAccount || config.burnAccountIsBlackhole || block._id % config.ecoBlocks !== 0)
                return rs(0)
            // offset inflation
            let rp = eco.rewardPool()
            let burnAmount = Math.floor(rp.dist)
            if (burnAmount <= 0)
                return rs(0)
            cache.findOne('accounts', { name: config.burnAccount }, (e, burnAccount) => {
                // do nothing if there is none to burn
                if (burnAccount.balance <= 0)
                    return rs(0)
                // burn only up to available balance
                burnAmount = Math.min(burnAmount, burnAccount.balance)
                cache.updateOne('accounts', { name: config.burnAccount }, { $inc: { balance: -burnAmount } }, () =>
                    transaction.updateGrowInts(burnAccount, block.timestamp, () => {
                        transaction.adjustNodeAppr(burnAccount, -burnAmount, () => {
                            logr.econ('Burned ' + burnAmount + ' periodically from ' + config.burnAccount)
                            return rs(burnAmount)
                        })
                    })
                )
            })
        })
    },
    calculateHashForBlock: (block) => {
        try {
            if (!block || !block._id) {
                throw new Error('Cannot calculate hash for invalid block: missing block or block._id')
            }
            
            // Make sure required fields exist
            const blockObj = {
                _id: block._id || 0,
                phash: block.phash || '',
                timestamp: block.timestamp || 0,
                txs: block.txs || [],
                miner: block.miner || '',
                missedBy: block.missedBy || '',
                steemblock: block.steemblock || 0
            }

            return chain.calculateHash(
                blockObj._id,
                blockObj.phash,
                blockObj.timestamp,
                blockObj.txs,
                blockObj.miner,
                blockObj.missedBy,
                blockObj.steemblock
            )
        } catch (error) {
            logr.error('Error calculating block hash:', error)
            throw error
        }
    },
    calculateHash: (index, phash, timestamp, txs, miner, missedBy, steemblock) => {
        let string = index + phash + timestamp + txs + miner
        if (missedBy) string += missedBy
        if (steemblock) string += steemblock

        return CryptoJS.SHA256(string).toString()
    },
    getLatestBlock: () => {
        return chain.recentBlocks[chain.recentBlocks.length - 1]
    },
    getFirstMemoryBlock: () => {
        return chain.recentBlocks[0]
    },
    cleanMemory: () => {
        chain.cleanMemoryBlocks()
        chain.cleanMemoryTx()
        eco.cleanHistory()
    },
    cleanMemoryBlocks: () => {
        if (config.ecoBlocksIncreasesSoon) {
            logr.trace('Keeping old blocks in memory because ecoBlocks is changing soon')
            return
        }

        let extraBlocks = chain.recentBlocks.length - config.ecoBlocks
        while (extraBlocks > 0) {
            chain.recentBlocks.shift()
            extraBlocks--
        }
    },
    cleanMemoryTx: () => {
        for (const hash in chain.recentTxs)
            if (chain.recentTxs[hash].ts + config.txExpirationTime < chain.getLatestBlock().timestamp)
                delete chain.recentTxs[hash]
    },
    applyHardfork: (block, cb) => {
        // Do something on hardfork block after tx executions and before leader rewards distribution
        // As this is not a real transaction, no actual transaction is considered executed here
        if (block._id === 17150000)
            // Clear @dtube.airdrop account
            cache.findOne('accounts', { name: config.burnAccount }, (e, burnAccount) => {
                let burned = burnAccount.balance
                cache.updateOne('accounts',
                    { name: config.burnAccount },
                    {
                        $set: {
                            balance: 0,
                            bw: { v: 0, t: block.timestamp },
                            vt: { v: 0, t: block.timestamp }
                        }
                    }, () => cb(null, { executed: false, distributed: 0, burned: burned })
                )
            })
        else
            cb(null, { executed: false, distributed: 0, burned: 0 })
    },

    batchLoadBlocks: (blockNum, cb) => {
        if (chain.blocksToRebuild.length === 0)
            if (blocks.isOpen) {
                chain.blocksToRebuild = blocks.readRange(blockNum, blockNum + max_batch_blocks - 1)
                cb(chain.blocksToRebuild.shift())
            } else
                db.collection('blocks').find({ _id: { $gte: blockNum, $lt: blockNum + max_batch_blocks } }).toArray((e, loadedBlocks) => {
                    if (e) throw e
                    if (loadedBlocks) chain.blocksToRebuild = loadedBlocks
                    cb(chain.blocksToRebuild.shift())
                })
        else cb(chain.blocksToRebuild.shift())
    },
    rebuildState: (blockNum, cb) => {
        // If chain shutting down, stop rebuilding and output last number for resuming
        if (chain.shuttingDown)
            return cb(null, blockNum)

        // Genesis block is handled differently
        if (blockNum === 0) {
            eco.history = [{ _id: 0, votes: 0, cDist: 0, cBurn: 0 }]
            chain.recentBlocks = [chain.getGenesisBlock()]
            chain.schedule = chain.minerSchedule(chain.getGenesisBlock())
            chain.rebuildState(blockNum + 1, cb)
            return
        }

        chain.batchLoadBlocks(blockNum, async (blockToRebuild) => {
            if (!blockToRebuild)
                // Rebuild is complete
                return cb(null, blockNum)

            // Validate block and transactions, then execute them
            if (process.env.REBUILD_NO_VALIDATE !== '1') {
                let isValidBlock = await chain.isValidNewBlockPromise(blockToRebuild, true, false)
                if (!isValidBlock)
                    return cb(true, blockNum)
            }
            chain.executeBlockTransactions(blockToRebuild, process.env.REBUILD_NO_VALIDATE !== '1', (validTxs, dist, burn) => {
                // if any transaction is wrong, thats a fatal error
                // transactions should have been verified in isValidNewBlock
                if (blockToRebuild.txs.length !== validTxs.length) {
                    logr.fatal('Invalid tx(s) in block found after starting execution')
                    return cb('Invalid tx(s) in block found after starting execution', blockNum)
                }

                // error if distributed or burned computed amounts are different than the reported one
                let blockDist = blockToRebuild.dist || 0
                if (blockDist !== dist)
                    return cb('Wrong dist amount ' + blockDist + ' ' + dist, blockNum)

                let blockBurn = blockToRebuild.burn || 0
                if (blockBurn !== burn)
                    return cb('Wrong burn amount ' + blockBurn + ' ' + burn, blockNum)

                // update the config if an update was scheduled
                chain.addRecentTxsInBlock(blockToRebuild.txs)
                config = require('./config.js').read(blockToRebuild._id)
                dao.nextBlock()
                daoMaster.nextBlock()
                eco.nextBlock()
                eco.appendHistory(blockToRebuild)
                chain.cleanMemory()
                leaderStats.processBlock(blockToRebuild)
                txHistory.processBlock(blockToRebuild)

                let writeInterval = parseInt(process.env.REBUILD_WRITE_INTERVAL)
                if (isNaN(writeInterval) || writeInterval < 1)
                    writeInterval = 10000

                cache.processRebuildOps(() => {
                    if (blockToRebuild._id % config.leaders === 0)
                        chain.schedule = chain.minerSchedule(blockToRebuild)
                    chain.recentBlocks.push(blockToRebuild)
                    chain.output(blockToRebuild, true)

                    // process notifications and leader stats (non blocking)
                    notifications.processBlock(blockToRebuild)

                    // next block
                    chain.rebuildState(blockNum + 1, cb)
                }, blockToRebuild._id % writeInterval === 0)
            })
        })
    },
    shutDown: () => {
        chain.shuttingDown = true
        chain.mining = false
    },
    signBlock: (block) => {
        let nextHash = chain.calculateHashForBlock(block)
        let signature = secp256k1.ecdsaSign(Buffer.from(nextHash, 'hex'), bs58.decode(process.env.NODE_OWNER_PRIV))
        signature = bs58.encode(signature.signature)
        return new Block(block._id, block.steemblock, block.phash, block.timestamp, block.txs, block.miner, block.missedBy, block.dist, block.burn, signature, nextHash)
    },
    createAccount: (name, pub, callback) => {
        // First check if account already exists to avoid duplicate creation
        cache.findOne('accounts', { name: name }, function (err, account) {
            if (err) {
                callback(err)
                return
            }
            
            if (account) {
                // Account already exists, silently return it
                callback(null, account)
                return
            }

            // Only create and log if account doesn't exist
            let newAccount = {
                name: name,
                pub: pub,
                balance: 0

            }

            cache.insertOne('accounts', newAccount, function(err) {
                if (err) {
                    callback(err)
                    return
                }
                
                // Log only once when actually creating a new account
                logr.info('Created account:', name)
                callback(null, newAccount)
            })
        })
    },
}

module.exports = chain
