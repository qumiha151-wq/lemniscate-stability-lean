import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [76,76,76,76,80,80,80,80,80,80,80,80,80,80,80,80]
  32820354633461541725795865246125953610360430290203785351165019827128799456326322893415718329285109044087624340622324774591163734423916571685572641007553 157039853299520939100559842730500473436327614174367952598118617866021779375764328420046781853613623034213274128113338653289531034346312243975015381711699 73855211510594062160038590585921400938839261672757277283222473159510462538773062264591940899830124403855186087843193264879185674551192090453659075934152 74280925346368644396127314090006900241453226951509781905508777732431997907137196284927617227989176455070252211325796301390265052372009246740480645597406

private def left : Mark := ⟨(-16410177316730770862897932623062976805180215145101892675582509913564399728163161446707859164642554522043812170311162387295581867211958285842786320503777),(-78519926649760469550279921365250236718163807087183976299059308933010889687882164210023390926806811517106637064056669326644765517173156121987507690855850),36927605755297031080019295292960700469419630836378638641611236579755231269386531132295970449915062201927593043921596632439592837275596045226829537967076,37140462673184322198063657045003450120726613475754890952754388866215998953568598142463808613994588227535126105662898150695132526186004623370240322798703⟩
private def right : Mark := ⟨(-59794795764210573225340386764479036495104378714322569627192632710664404489620239209500786577876840643987202693663761736504666210264541492229508532893756),(-92924397092772391489029489508469007559131165228310183695331603550511154120123403030383637301272874405267875777605622708963096675024795387772391028994641),47595393140843688740025604303853233960963514722813467894446094602429451822758045712785355363122383953222589526387015007419953392728666116288189637507674,21857277647625147177992603483293830370623066968067419369633912773223020776038144364350967571777311030232651505410184937139939144363565709761765705346473⟩

private theorem cell0 : Transports 48 49 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 48 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 49 50 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 49 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 50 51 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 50 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 51 52 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 51 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 52 53 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 52 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 53 54 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 53 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 54 55 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 54 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 55 56 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 55 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 56 57 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 56 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 57 58 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 57 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 58 59 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 58 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 59 60 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 59 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 60 61 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 60 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 61 62 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 61 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 62 63 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 62 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 63 64 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 63 _ _ (by decide) (by decide +kernel)

theorem positive_transport_48_64 : Transports 48 64 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_48_64
