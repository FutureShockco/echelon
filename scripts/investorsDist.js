const MongoClient = require('mongodb').MongoClient;
const assert = require('assert');

var investors = [
    ['mar1u5february', 150000],
    ['pigpig1984', 103493],
    ['caspper5910', 100050],
    ['locomb24th', 59607],
    ['yutoaopan', 32000],
    ['zerox23x0', 30000],
    ['adetorrent', 30000],
    ['mvd', 29498],
    ['joko1980llk', 22000],
    ['chryptos22', 21500],
    ['adulteducation99', 20247],
    ['just.clown00', 20050],
    ['feruz4444', 20000],
    ['hauptmann', 18056],
    ['dabiggest01', 12214],
    ['inertia', 10000],
    ['nestegg2020', 10000],
    ['sushirotor777', 10000],
    ['prc', 10000],
    ['bonboni20', 10000],
    ['satoshi0124', 10000],
    ['4you2watch', 10000],
    ['ihave100000000', 9925],
    ['coupsdebambous', 7500],
    ['0bujuben0', 7000],
    ['stash1866', 7000],
    ['tibfox', 6733],
    ['captainbob', 6195],
    ['aaviator12785', 5500],
    ['cryptospa', 5000],
    ['ortegavalve11', 5000],
    ['anomadsoul', 5000],
    ['xrptsbridge589', 5000],
    ['blockchainbane01', 5000],
    ['tommyether01', 5000],
    ['joegoogle123', 4900],
    ['talentfinder01', 4777],
    ['dailydogger', 4228],
    ['matt00dtube', 3919],
    ['chat.video.live789', 3541],
    ['darkninjas04', 3500],
    ['phoneinf', 3222],
    ['captainmo369', 3221],
    ['binarydrool01', 3045],
    ['d00k13', 2982],
    ['1719grants6822evil', 2899],
    ['wofilobi0815', 2500],
    ['elsiekjay', 2418],
    ['igormuba', 2270],
    ['steeminator3000', 2218],
    ['immortalgamer01', 2000],
    ['gamechanger2020', 2000],
    ['atlantian.wizard1337', 2000],
    ['ndk.focus.00', 2000],
    ['kedar27', 2000],
    ['robertandrew01', 2000],
    ['russia-btc', 2000],
    ['tonytctn01', 1967],
    ['jeronimorubio', 1750],
    ['mrun1v3rs3', 1700],
    ['buttcoins', 1507],
    ['truthonlytruth88', 1500],
    ['dtubefr33dom', 1500],
    ['manniman', 1500],
    ['sailor206', 1400],
    ['esantra03', 1400],
    ['anarchistbanjo', 1350],
    ['acidyo', 1337],
    ['adventuroussoul', 1240],
    ['peaceofmind2020', 1111],
    ['mauriciovite', 1061],
    ['ohs33deeguy', 1019],
    ['bleuxwolf', 1010],
    ['awakenedhuman369', 1000],
    ['terraflux88', 1000],
    ['ev0luti0n', 1000],
    ['michealb', 1000],
    ['newyork101', 1000],
    ['chinaliu88', 1000],
    ['beunconstrained19', 1000],
    ['hookonair2020', 1000],
    ['hackylin1252', 1000],
    ['m3hrl1cht', 1000],
    ['teardrop66', 1000],
    ['flynneastwood', 1000],
    ['2020vision', 1000],
    ['1337-dude', 1000],
    ['abstractalao79', 1000],
    ['alimama1688', 1000],
    ['independent.network.00', 1000],
    ['patulda1974', 1000],
    ['alibaba1688', 1000],
    ['20minutes', 1000],
    ['smithereens888', 1000],
    ['brokensystem20', 1000],
    ['khimgoh', 1000],
    ['menaskop01', 1000],
    ['theinvestorsmind31', 1000],
    ['doncrypto00', 1000],
    ['humblenorthman777', 1000],
    ['duncanturk00', 1000],
    ['ramengirl', 1000],
    ['panthaproduction93', 953],
    ['greentoblue247', 950],
    ['rt-international', 909],
    ['curtis.arnold03', 900],
    ['iamthankfultom12', 900],
    ['buzzer11', 870],
    ['anderssinho', 866],
    ['twillis82', 800],
    ['truthrevonet', 800],
    ['hiscens10n', 800],
    ['samstonehill', 796],
    ['team-mexico', 776],
    ['jlsplatts', 775],
    ['louisecooksey00', 750],
    ['belimitless', 750],
    ['jiuzidt776', 690],
    ['87hawik78', 650],
    ['derzerb00', 650],
    ['calipso10', 650],
    ['waybeyondpadthai', 650],
    ['synthacon88', 608],
    ['dqdesoquaddub22', 576],
    ['agotube99', 555],
    ['thisiscrazy19', 550],
    ['felt.buzz', 530],
    ['skeenee', 527],
    ['distantsignal', 500],
    ['verglas', 500],
    ['nateaguila', 500],
    ['daan', 500],
    ['awco1988sanpedro', 500],
    ['kirpy0x', 500],
    ['robertandrew', 500],
    ['mrflower74', 500],
    ['amsoildealer', 500],
    ['joythewanderer', 500],
    ['cagyjan', 500],
    ['blockchaindeveloper81', 500],
    ['gardner00', 500],
    ['supermarmot99', 500],
    ['nikolayy1123', 500],
    ['x0zzsuho1', 500],
    ['nonsowrites', 500],
    ['sergiomendes', 500],
    ['bvramlow', 500],
    ['tanbay', 500],
    ['han5hain5dtube', 500],
    ['alexliu007', 500],
    ['52yongming', 500],
    ['heirofsigma88', 490],
    ['rehan12', 489],
    ['magenis01', 488],
    ['nicvander77', 465],
    ['c0ff33time', 450],
    ['ginofoto.09', 450],
    ['knowhow92', 437],
    ['zslzslzslzsl53', 422],
    ['nicolcron', 420],
    ['cxmatias01', 417],
    ['bartheek', 400],
    ['znnuksfe', 400],
    ['vladtepesblog', 400],
    ['gregscuderia89', 400],
    ['smilingdragon19', 400],
    ['dragraff', 370],
    ['g0ual3x1r', 369],
    ['vikingshd23', 360],
    ['emiliomorles', 351],
    ['loguidtube88', 350],
    ['freecrypto', 350],
    ['aleksandr13', 346],
    ['dromihete61', 341],
    ['kaerpediem', 333],
    ['jerokiah82', 300],
    ['cardboard', 300],
    ['old-guy-photos', 300],
    ['kevinturnbull', 300],
    ['0x64peym4n', 300],
    ['donworry8', 300],
    ['tisko', 250],
    ['axientas007', 250],
    ['chcornwe11', 250],
    ['mydtube2020today', 250],
    ['jongolson', 250],
    ['hexcrow3641', 250],
    ['sumatranate', 250],
    ['tubealts2020', 250],
    ['mstafford', 250],
    ['thegriot1257', 245],
    ['davixesk8', 235],
    ['stephenjudge00', 222],
    ['vsatyanaveen25', 200],
    ['ashtv', 200],
    ['simco25trade', 200],
    ['0ne-zero-0ne', 200],
    ['0doctorrobinson0', 200],
    ['treehousemedia247', 200],
    ['peppermint777', 200],
    ['someone13', 200],
    ['martial01', 200],
    ['hafizullah', 200],
    ['varioso12', 200],
    ['empath', 200],
    ['semerick99', 200],
    ['senatorlaw106', 200],
    ['pucvola2019', 200],
    ['humanearl', 200],
    ['brewcitygardener', 200],
    ['imcryptohustler101', 200],
    ['gewehr', 199],
    ['estefanobm12', 180],
    ['moderndayhippie', 165],
    ['elprutest', 165],
    ['yummyrecipe', 164],
    ['diamonds4ever', 163],
    ['katamori', 153],
    ['dinsha', 151],
    ['olopezdeveloper', 150],
    ['denissandmann11', 150],
    ['koalaslippy', 150],
    ['engrsayful', 150],
    ['afrinsultana', 150],
    ['cryptoastronaut9000', 150],
    ['nehasajan11', 145],
    ['templ8t0r', 144],
    ['anthonyadavisii', 127],
    ['steemersayu907', 125],
    ['doodle2020', 125],
    ['hungrypb', 125],
    ['luffy3333', 120],
    ['ficcion', 120],
    ['priyanarc', 120],
    ['danmaruschak', 110],
    ['hhayweaver', 110],
    ['louis0924', 110],
    ['kevkosta333', 110],
    ['notimedadmedia01', 105],
    ['ozelot47', 101],
    ['swent.art2020', 100],
    ['cryptofinally', 100],
    ['ultratrain1512', 100],
    ['summisimeon10', 100],
    ['ps1onrac1ng', 100],
    ['dantes2019', 100],
    ['fashionablebeauty00', 100],
    ['audiob00ks', 100],
    ['tshelby007', 100],
    ['davnem2020', 100],
    ['mconnors4343', 100],
    ['aquertyty12', 100],
    ['jameshwang77', 100],
    ['nisiryancruz05', 100],
    ['dominique7260', 100],
    ['vladimir1990', 100],
    ['okilix', 100],
    ['alokkumar121', 100],
    ['4dnine4d9', 100],
    ['cryptomajster74', 100],
    ['cpoliticas77', 100],
    ['jpwright89', 100],
    ['visionaer3003', 100],
    ['logicptk101', 100],
    ['veltelcom99', 100],
    ['hauzerphd99', 100],
    ['alionessart83', 100],
    ['slayerkm', 100],
    ['yanirauseche', 100],
    ['51decpbtc', 100],
    ['kofibeatz777', 100],
    ['c1ust4he4d', 100],
    ['fozdru006', 100],
    ['k-banti', 100],
    ['20mariomfarinato', 110],
    ['emsonic', 100],
    ['parisfoodhunter75', 100],
    ['salomon61', 100],
    ['1ronaper1', 100],
    ['bizzle2191', 100],
    ['menestrello00', 100],
    ['natural20', 100],
    ['fasolo97', 100],
    ['thedoctor95', 100],
    ['mautes', 100],
    ['clove71', 100],
    ['1dtubemusic1', 100],
    ['theguruasia', 100],
    ['gamer00', 100],
    ['tortulez85', 100],
    ['rangertx', 100],
    ['unacomn42', 100],
    ['merisaari00', 100],
    ['mirusev72', 100],
    ['lennon.life', 100],
    ['7love-over-gold.org7', 92],
    ['carpetrading77', 89],
    ['afsar3501', 87],
    ['ammonite', 81],
    ['pocketnet99', 80],
    ['neladepablos', 74],
    ['davixesk8', 73],
    ['worldtraveller32', 70],
    ['dalz1elmus1c', 70],
    ['elteamgordo', 70],
    ['certain', 70],
    ['carlos-fernando', 58],
    ['lordjeijo', 55],
    ['stoicho88', 53],
    ['shaidon', 52],
    ['krazypoet', 50],
    ['djefferys926', 50],
    ['sgt-dan', 50],
    ['realyoni22', 50],
    ['kirasung65', 50],
    ['c7229d314104b44', 50],
    ['kokoliso', 50],
    ['gurkandraman1968', 50],
    ['batatudo1999', 50],
    ['blahuman88', 50],
    ['pachu', 50],
    ['xr-hammergaming', 50],
    ['andyx5silver1', 50],
    ['fastidiousdisseminations222', 50],
    ['pabrasey44', 50],
    ['theshouhu21', 50],
    ['21conspiracy', 50],
    ['haroonimran00', 50],
    ['jeunesseglobal.alexandre.buffat66', 50],
    ['raikkizulu01', 50],
    ['slow-mok125', 50],
    ['plane3eye3', 50],
    ['nonelilian00', 50],
    ['dexpartacus', 50],
    ['xyz123456', 50],
    ['d3c3ntralized', 50],
    ['greencross', 50],
    ['dumitru88', 50],
    ['scottlynnd19', 50],
    ['sharingiscaring98', 50],
    ['clfund4poor1', 50],
    ['saboin', 50],
    ['y2krang1983', 50],
    ['mark-v0220', 50],
    ['cloudvitter12', 50],
    ['editzon', 50],
    ['lifeprint.fit30', 50],
    ['andage001', 50],
    ['ace108', 50],
    ['panoslagog23', 50],
    ['brightvibes', 50],
    ['skorobogatov001', 50],
    ['smaugh04r', 50],
    ['lolakers365', 50],
    ['uivlisup2eat4lunch', 50],
    ['madushanka', 50],
    ['summercloud00', 50],
    ['maxcert74', 50],
    ['reimerlin', 50],
    ['badger666', 50],
    ['bennett42', 50],
    ['amithecool1yetorami2cool', 50],
    ['bobaphet', 50],
    ['eulices31', 50],
    ['coyotemopar00', 50],
    ['awaking12', 50],
    ['mkmangold62', 50],
    ['slojin123', 50],
    ['oheyo', 50],
    ['nof1', 50],
    ['dikanevn77', 50],
    ['e-cryptomastery.com11', 50],
    ['thekitchenfairy', 50],
    ['dzeypee', 50],
    ['naturschnitzerl61', 50],
    ['24life-techno', 50],
    ['kenny-crane', 50],
    ['vollero00orellov', 50],
    ['krissysmith16', 50],
    ['jza', 50],
    ['macron', 50],
    ['flightlessballer14', 50],
    ['elements55', 50],
    ['vilivision2020', 50],
    ['marleytat666', 50],
    ['blommah74', 50],
    ['mike.rod', 50],
    ['mike.rod', 50],
    ['1thebiochemist1', 50],
    ['xmellowgoldx888', 50],
    ['marshall007', 50],
    ['silent2020', 50],
    ['celestin259', 50],
    ['brendan1hm1g', 50],
    ['raydaman00', 50],
    ['xavi0rfx1', 50],
    ['sc00tertv', 50],
    ['duckm4st3r', 50],
    ['jas0nj0rdan', 50],
    ['mistakili', 50],
    ['emeraldway74', 50],
    ['anthillart01', 50],
    ['kenanqhd', 50],
    ['matejkojc20', 50],
    ['mobi4speed1', 50],
    ['palhoto', 50],
    ['ondra.cesko.81', 50],
    ['firayumni99', 50],
    ['norulers96', 50],
    ['edb', 50],
    ['iwarp0001', 50],
    ['iamraincrystal', 50],
    ['dconnect312', 50],
    ['turchik777', 50],
    ['anoophallur11', 50],
    ['pepemadrid100', 50],
    ['r0d', 50],
    ['bestsmoothjazz', 50],
    ['blackdynamite45', 50],
    ['etblink87', 50],
    ['limestone999', 50],
    ['ignacioarreses', 49],
    ['tantrum', 40],
    ['pixiepost', 40],
    ['telemak00', 38],
    ['adrianpza0512', 38],
    ['erick1', 36],
    ['hammer927', 35],
    ['snmelinger', 34],
    ['generaljoker05', 30],
    ['voxmortis', 30],
    ['krishnakuya15', 30],
    ['alexvanaken', 30],
    ['gameplay00', 30],
    ['adambarratt', 30],
    ['imaugedessturms2033', 30],
    ['nannal', 28],
    ['crypt0unic0rn', 26],
    ['denizcakmak', 26],
    ['steemshiro69', 25],
    ['k3inni3mand', 25],
    ['captainklaus', 23],
    ['max888888', 22],
    ['cryptichybrid', 21],
    ['quantum-cyborg', 21],
    ['captaincryptonite777', 20],
    ['chrisamuda', 20],
    ['vlcbsmdv77', 20],
    ['byercatire', 20],
    ['ab0x0fcream', 20],
    ['snook', 20],
    ['topperz101', 20],
    ['suraj1997', 20],
    ['normnav01', 20],
    ['beats4change', 20],
    ['kiwibloke', 20],
    ['josediccus', 16],
    ['dappuser01', 15],
    ['erode', 15],
    ['gaionaus16', 14],
    ['star.citizen', 14],
    ['simms50', 13],
    ['dj.alx.396', 13],
    ['clixmoney', 12],
    ['goblin1234', 11],
    ['nerdtopiade', 11],
    ['gurujames20', 10],
    ['gaborockstar', 10],
    ['yonnathang', 10],
    ['ragnarokdel', 10],
    ['flaxz', 10],
    ['onealfa', 10],
    ['abdt', 10],
    ['smarttj88', 10],
    ['c0st0m1s3', 10],
    ['shogo', 10],
    ['heimindanger', 10],
    ['destroyedarkana01', 10],
    ['clubdeloslocos2020', 10],
    ['anonymouslyfunny22', 10],
    ['ivansnz', 10],
    ['memoryleakdeath', 10],
    ['hungryharish', 10],
    ['ackza', 10],
    ['ourhappyplace', 10],
    ['bonzopoe', 10],
    ['putu300', 10],
    ['chetanpadliya', 10],
    ['drfk', 10],
    ['leptiri11', 10],
    ['cmroks', 10],
    ['wehmoen', 10],
    ['gassa28', 10],
    ['justinashby81', 8],
    ['walterprofe', 8],
    ['rolrien', 5],
    ['dolcesalato1981', 5],
    ['sweettais44', 5],
    ['toufiq777', 5],
    ['vickaboleyn', 5],
    ['technologix22', 5],
    ['sathya001', 5],
    ['airdroponmobile10', 5],
    ['athomewithcraig', 5],
    ['c0nqrfr0mwithin', 5],
    ['omar-hesham1983', 4],
    ['outtheshellvlog', 4],
    ['loler555', 4],
    ['laparejab1tc0in', 4],
    ['webresultat19', 4],
    ['marques-brownlee', 2],
    ['engineermabbas11', 2],
    ['zoeykaely', 2],
    ['midnightthoughts', 2],
    ['postfach1679', 2],
    ['swiss-authority', 2],
    ['andrew2200us', 2],
    ['alpayasteem', 2],
    ['edulibrary', 1],
    ['lenarose', 1],
    ['zhother', 1],
    ['amazing-things', 1],
    ['qam2112tube', 1],
    ['transisto00', 1],
    ['dtuber789', 1],
    ['jalentakesphotos', 1],
    ['daddycosmic', 1],
    ['life-is-gg-music', 1],
    ['rasengan', 1],
    ['braveleague', 1],
    ['life-is-gg-00', 1],
    ['roshne', 1],
    ['mr.spice.0.0', 1],
    ['electronichobbyworks00', 1],
    ['kusoneko01', 1],
    ['infobyte87', 1],
    ['abdulmutahar12', 1],
    ['life-is-gg', 1],
    ['anurag11', 1],
    ['jkramer', 1],
    ['panza', 1],
    ['alexsandr', 1],
    ['shaidon57', 1]
]

var totalDTC = 0
for (let i = 0; i < investors.length; i++) {
    totalDTC += investors[i][1]
}
console.log(totalDTC)

// Connection URL
const url = 'mongodb://localhost:27017';
 
// Database Name
const dbName = 'echelon2';
 
// // Use connect method to connect to the server
MongoClient.connect(url, {useUnifiedTopology: true}, function(err, client) {
    assert.equal(null, err);
    console.log("Connected successfully to server");
    
    db = client.db(dbName);

    console.log(investors.length)
    for (let i = 0; i < investors.length; i++) {
        deliver(investors[i])
    }
 
//   client.close();
});

var totalDist = 0
function deliver(investor) {
    var username = investor[0].replace('@','').toLowerCase().trim()
    var amount = investor[1]*100
    totalDist += amount
    
    console.log(username, amount, totalDist)
    db.collection('accounts').findOne({name: username}, function(err, res) {
        if (err) throw err;
        if (!res) throw 'no account for '+username
        db.collection('accounts').updateOne({name: username}, {$inc: {balance: investor[1]*100}}, function(err, res) {
            if (!res.matchedCount)
                console.log('didnt match')
            // else console.log(username+' ok')
            if (err) throw err;
        })
    })
}