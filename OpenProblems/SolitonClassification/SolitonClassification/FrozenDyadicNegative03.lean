import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [80,80,80,80,80,80,80,80,80,80,80,80,80,80,80,80]
  131598779158576994868437209090103794849425652377106210230421637678660681020350069535056665810015283809344529577856577800102344704309732173698376407931125 111947438672278764122468528645417876768735416842828994119333777471374796978615031539068322563498281998708872011176841202963944374095759197814075721583189 64472759041005901616383895256220664856237616235589014940263760956007876816495416769637831624138145423925888191574326823921324647284366057873188037183584 82556111095592245925385538044975003930619250811974328724765938621313314068801497392164489907910974770993304239942550269122074432826108101353121565997375

private def left : Mark := ⟨(-65799389579288497434218604545051897424712826188553105115210818839330340510175034767528332905007641904672264788928288900051172352154866086849188203965563),(-55973719336139382061234264322708938384367708421414497059666888735687398489307515769534161281749140999354436005588420601481972187047879598907037860791595),32236379520502950808191947628110332428118808117794507470131880478003938408247708384818915812069072711962944095787163411960662323642183028936594018591792,(-41278055547796122962692769022487501965309625405987164362382969310656657034400748696082244953955487385496652119971275134561037216413054050676560782998688)⟩
private def right : Mark := ⟨(-86993813911190085953988200286296346177709644672744008931260929121211404176845141804969041559203079943613124097792223565455834457513496420508004925874208),(-19815941672844376794963163730544078849682580545846714023205225364850586764951569668720990852943025718403084609103915413178099883150671174170393522652524),(-4222244766038299849350091867606366213724552596813410297513501645825995028682338743160120393869708928405626816873741366037121660114344512920384030625882),(-52203780356718482808591414775640531950929502342476849903531169143987818409424914409752304788656639284865231294886204070328588230154348281172427513078874)⟩

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

theorem negative_transport_48_64 : Transports 48 64 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_48_64
