import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [80,80,80,80,80,80,80,80,80,80,80,80,80,80,80,80]
  80903719006403034233429164788243666152827681558657152448604270551548133687689231335884050986932164217959530688944016472067481299921486826816023991888799 197942722654716146044634934887255162201284792361629899948639396642352709437905350606610707996673544945261220627367999290112708613727187911989050774048104 104445095271810489598099391794245687036696706485518281102053021495597435480162437869773148744847936402880250404853832012501484821807696111368819032718307 7966819393572787431933978234550702617374303378249782093628690020595032675169632653107059648610493785626058786104890312803378186230287146230137349244139

private def left : Mark := ⟨(-40451859503201517116714582394121833076413840779328576224302135275774066843844615667942025493466082108979765344472008236033740649960743413408011995944400),98971361327358073022317467443627581100642396180814949974319698321176354718952675303305353998336772472630610313683999645056354306863593955994525387024052,(-52222547635905244799049695897122843518348353242759140551026510747798717740081218934886574372423968201440125202426916006250742410903848055684409516359154),(-3983409696786393715966989117275351308687151689124891046814345010297516337584816326553529824305246892813029393052445156401689093115143573115068674622070)⟩
private def right : Mark := ⟨16071623950964168919677975309326395837112492140204848170812205180498476698902657786865079053821700355675413602330690568136444791367974387884457320577260,126275064960478990706404820849020558770403253915977940789560353189999719338412325813636881707056876521140156459760766760424228342206253197711900242841360,(-52306241791933707306108651795299941843632741553092572310968202667537190793427299869735755711826636477656014769484006273777691183260272847713692020602069),2668164912559194440658103068872648418570133286931968178556140304477998491064831764435499669029296732258036202342492685322594957140360578118652305574487⟩

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

theorem negative_transport_96_112 : Transports 96 112 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_96_112
