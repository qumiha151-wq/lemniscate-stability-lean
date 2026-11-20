import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [84,84,84,84,84,84,84,84,84,84,84,84,84,84,84,84]
  219041166655245402168989987325194621680371883566752926285971967981230412522927636582551238745670050719254274305665346836596527058605477454846512003587635 86280535840579523317150650588087941289675829486418603523073450969870094424455504998884279760707162636687814514902987280431020026161139358665669662769160 16803037510709915029989836238696147854213391867896530561246298877405116676534664081441506786868956062469074823655514878700840010519077679444533316428256 103392001953734568881426700780791656869609689622109779831516419077843819774445609541402914008534038921326952504885501114587893897545967351312334979733207

private def left : Mark := ⟨(-109520583327622701084494993662597310840185941783376463142985983990615206261463818291275619372835025359627137152832673418298263529302738727423256001793818),43140267920289761658575325294043970644837914743209301761536725484935047212227752499442139880353581318343907257451493640215510013080569679332834831384580,8401518755354957514994918119348073927106695933948265280623149438702558338267332040720753393434478031234537411827757439350420005259538839722266658214128,(-51696000976867284440713350390395828434804844811054889915758209538921909887222804770701457004267019460663476252442750557293946948772983675656167489866604)⟩
private def right : Mark := ⟨(-64820659036789064406767575428605235777575471426448500846034783055200823976927472215258569623010879259412541283735057427295231805901130616231746205589386),122573650940476128196234573446038963983355201567283318551582261870851843266873916133266929204248695375427837529614179328815921140440362678783445809818924,(-33849505191921408969390005894248249615600570752553802518048726567214369695479391742679090676962235816669681133442121660706617368386980134340315993458176),(-39965898371723485127032148844448430387764257496882203095527324896623013921630879171205629150557166914490644682284825023650209420698417143814764880857559)⟩

private theorem cell0 : Transports 96 97 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 96 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 97 98 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 97 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 98 99 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 98 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 99 100 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 99 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 100 101 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 100 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 101 102 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 101 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 102 103 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 102 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 103 104 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 103 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 104 105 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 104 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 105 106 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 105 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 106 107 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 106 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 107 108 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 107 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 108 109 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 108 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 109 110 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 109 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 110 111 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 110 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 111 112 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 111 _ _ (by decide) (by decide +kernel)

theorem positive_transport_96_112 : Transports 96 112 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_96_112
