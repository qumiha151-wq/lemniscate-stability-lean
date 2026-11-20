import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,100,100,100,100,100,100,104,104,104,104,104,104,104]
  61308010494883710994207464521838370300176244798421134898054134144526282132444338469624735922574961801301604456069726704453961700795287623220612686968678 906380085998550789579930134136512356235011326355424954137212134892479317052395468177997518360672199295736951079311710245713460490873687922232781014717628 99008618676966127132113868419607843487441807355459707667664524952789763329699311490034389350039861245408748528077166041537608319405194528956477442791553 34198560865429579475489364541668803053897037619292171249153573894298755120568730271276142048223244575180074132858965622354633847586635184337720229876985

private def left : Mark := ⟨30654005247441855497103732260919185150088122399210567449027067072263141066222169234812367961287480900650802228034863352226980850397643811610306343484339,453190042999275394789965067068256178117505663177712477068606067446239658526197734088998759180336099647868475539655855122856730245436843961116390507358814,(-49504309338483063566056934209803921743720903677729853833832262476394881664849655745017194675019930622704374264038583020768804159702597264478238721395777),(-17099280432714789737744682270834401526948518809646085624576786947149377560284365135638071024111622287590037066429482811177316923793317592168860114938493)⟩
private def right : Mark := ⟨217877873119184784167982407995873452180885653267792556946501741136732700438436316855413540653548481723845173149674377168863878111422847938265499698950772,117930221286430986549737047993626689598400793643870957454164082009891162309978891943473539878163099680398861099495602323275625387224079241622043947893270,3617752892825127310283568121647265254956561940417424753773259678327548637467023536079685246754738719976738631811033435218428808821996583629949334932634,(-52249152130951366898633433113618609823909055198716690233774277511630889268508980781349003445438044471037066935955732118267732910783064654793370630443678)⟩

private theorem cell0 : Transports 432 433 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 432 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 433 434 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 433 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 434 435 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 434 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 435 436 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 435 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 436 437 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 436 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 437 438 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 437 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 438 439 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 438 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 439 440 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 439 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 440 441 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 440 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 441 442 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 441 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 442 443 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 442 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 443 444 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 443 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 444 445 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 444 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 445 446 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 445 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 446 447 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 446 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 447 448 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 447 _ _ (by decide) (by decide +kernel)

theorem positive_transport_432_448 : Transports 432 448 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_432_448
