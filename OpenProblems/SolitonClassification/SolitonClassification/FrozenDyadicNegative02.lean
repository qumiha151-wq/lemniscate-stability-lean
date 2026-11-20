import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [76,76,76,76,76,76,76,76,80,80,80,80,80,80,80,80]
  76884313911224251371906546394771441620199184788781985572572721853335969938176525460430578766194444510752306255776750047948234751970512768941411203269341 97450120667635823446404503402651574647433068483169666998364046844062202245533884889766336191201762677226241754332914810557727994788177340843808375310255 95928665709475121122276990767083141614702865944295839556980148680790160536743205419643410112428602428118477969362391433740639955371516433013794547642994 42070645737701120092255721971090407450715720395802115376050243914946094717548068364861799485919824572634589363948095983680966222345115821461816252871239

private def left : Mark := ⟨(-38442156955612125685953273197385720810099592394390992786286360926667984969088262730215289383097222255376153127888375023974117375985256384470705601634671),(-48725060333817911723202251701325787323716534241584833499182023422031101122766942444883168095600881338613120877166457405278863997394088670421904187655128),47964332854737560561138495383541570807351432972147919778490074340395080268371602709821705056214301214059238984681195716870319977685758216506897273821497,(-21035322868850560046127860985545203725357860197901057688025121957473047358774034182430899742959912286317294681974047991840483111172557910730908126435620)⟩
private def right : Mark := ⟨(-65799389579288497434218604545051897424712826188553105115210818839330340510175034767528332905007641904672264788928288900051172352154866086849188203965563),(-55973719336139382061234264322708938384367708421414497059666888735687398489307515769534161281749140999354436005588420601481972187047879598907037860791595),32236379520502950808191947628110332428118808117794507470131880478003938408247708384818915812069072711962944095787163411960662323642183028936594018591792,(-41278055547796122962692769022487501965309625405987164362382969310656657034400748696082244953955487385496652119971275134561037216413054050676560782998688)⟩

private theorem cell0 : Transports 32 33 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 32 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 33 34 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 33 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 34 35 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 34 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 35 36 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 35 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 36 37 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 36 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 37 38 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 37 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 38 39 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 38 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 39 40 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 39 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 40 41 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 40 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 41 42 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 41 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 42 43 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 42 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 43 44 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 43 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 44 45 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 44 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 45 46 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 45 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 46 47 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 46 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 47 48 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 47 _ _ (by decide) (by decide +kernel)

theorem negative_transport_32_48 : Transports 32 48 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_32_48
