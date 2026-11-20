import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [84,84,84,84,80,80,80,80,80,80,80,80,80,80,80,80]
  129641318073578128813535150857210471555150942852897001692069566110401647953854944430517139246021758518825082567470114854590463611802261232463492411178771 245147301880952256392469146892077927966710403134566637103164523741703686533747832266533858408497390750855675059228358657631842280880725357566891619637848 67699010383842817938780011788496499231201141505107605036097453134428739390958783485358181353924471633339362266884243321413234736773960268680631986916351 79931796743446970254064297688896860775528514993764406191054649793246027843261758342411258301114333828981289364569650047300418841396834287629529761715117

private def left : Mark := ⟨(-64820659036789064406767575428605235777575471426448500846034783055200823976927472215258569623010879259412541283735057427295231805901130616231746205589386),122573650940476128196234573446038963983355201567283318551582261870851843266873916133266929204248695375427837529614179328815921140440362678783445809818924,(-33849505191921408969390005894248249615600570752553802518048726567214369695479391742679090676962235816669681133442121660706617368386980134340315993458176),(-39965898371723485127032148844448430387764257496882203095527324896623013921630879171205629150557166914490644682284825023650209420698417143814764880857559)⟩
private def right : Mark := ⟨3897807340232060446616828316774903960787877077596444854446769016729691741737229738714132626437207223404152782890071516821121010212196181044624713645322,149353852670785016264146772768242407806971168079658405487327090493649858693758725826788404721588627725980677200907760624169417819906086180551823166659582,(-44177597136900848692575426956937387687659364163584307499151008256505897180473945648295266980938182936156650070051918127717599014065754784937486642143164),(-28131867083550182981249422020815052096050096035018332839038640557998723419155286322571864414467480064677603272131632334929461385120664828022932367035530)⟩

private theorem cell0 : Transports 112 113 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 112 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 113 114 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 113 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 114 115 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 114 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 115 116 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 115 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 116 117 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 116 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 117 118 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 117 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 118 119 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 118 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 119 120 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 119 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 120 121 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 120 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 121 122 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 121 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 122 123 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 122 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 123 124 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 123 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 124 125 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 124 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 125 126 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 125 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 126 127 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 126 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 127 128 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 127 _ _ (by decide) (by decide +kernel)

theorem positive_transport_112_128 : Transports 112 128 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_112_128
