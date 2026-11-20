import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,104,100,100,100,100,100,100,100,100,100,96,96]
  399423414840842755837456250175547231239771822812950903546269806638255967172759841927696312509319714359955046828427091289485258280903108949276548104934388 154975984682497714400010032931485238107215788442271740605008069754012843854583975535216557500790579003951447711096734474100372516551319836216806834135498 22286047225087387254765826452757762516773430247756976880704606174450260057986729741894862443564808991653017155472464434406086306945181546444984013550163 102350282054660465566308599621796291096025318217980964550879405599272458295041982030310026234517088940899117121389234987351037677454699418289221259987811

private def left : Mark := ⟨199711707420421377918728125087773615619885911406475451773134903319127983586379920963848156254659857179977523414213545644742629140451554474638274052467194,77487992341248857200005016465742619053607894221135870302504034877006421927291987767608278750395289501975723855548367237050186258275659918108403417067749,(-11143023612543693627382913226378881258386715123878488440352303087225130028993364870947431221782404495826508577736232217203043153472590773222492006775082),(-51175141027330232783154299810898145548012659108990482275439702799636229147520991015155013117258544470449558560694617493675518838727349709144610629993906)⟩
private def right : Mark := ⟨88078206152744653540819899607626463089907293684636813833310664074811788417897655016882362378715428566900908038059547050338517931392134276206816940025410,(-393312428653854399622437716216101624754466835867010265045187207520885984189296216111710036381837151061191230420427117498022741819755429259560368043878787),51120512820274069219179907494448035951751974180363187233898722937419881259426222352636896672177781492398574478551102340541859570486503709594303059250072,(-11391014151033211281785554809059911506198559878074878125615072008286511443361906305582622518080411781120230767126055826763361200667822218619194737375700)⟩

private theorem cell0 : Transports 352 353 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 352 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 353 354 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 353 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 354 355 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 354 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 355 356 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 355 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 356 357 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 356 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 357 358 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 357 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 358 359 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 358 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 359 360 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 359 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 360 361 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 360 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 361 362 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 361 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 362 363 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 362 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 363 364 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 363 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 364 365 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 364 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 365 366 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 365 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 366 367 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 366 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 367 368 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 367 _ _ (by decide) (by decide +kernel)

theorem negative_transport_352_368 : Transports 352 368 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_352_368
