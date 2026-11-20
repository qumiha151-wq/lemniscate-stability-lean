import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,104,104,108,108,108,108,108,108,108,108,108,108]
  266442153755829744726269763180684573923558026293095913147026222539262796833703348583392052256516164032266467600016737420947926979748719413052333422249337 968237335260682610310333576239372353846012783585178391499887331149451841903651050075666446114225950748330743399970698354990792708387745320007288691409217 97609095939116222752974268110677999573820783140031760417184247405489153747812130438656858753081369615719643832237248746088350752723086776959837836995956 38009374206053199358692647259410525691712417908324610301531331715177898112788906846082012081440591143944993620881752789577548679376010863750385518542615

private def left : Mark := ⟨(-133221076877914872363134881590342286961779013146547956573513111269631398416851674291696026128258082016133233800008368710473963489874359706526166711124669),(-484118667630341305155166788119686176923006391792589195749943665574725920951825525037833223057112975374165371699985349177495396354193872660003644345704609),48804547969558111376487134055338999786910391570015880208592123702744576873906065219328429376540684807859821916118624373044175376361543388479918918497978,(-19004687103026599679346323629705262845856208954162305150765665857588949056394453423041006040720295571972496810440876394788774339688005431875192759271308)⟩
private def right : Mark := ⟨(-202393133874577452609333139604212602292012662984476098617537558016223135007223732617515723048792032973350731109369384576140075768670139464356376711720332),345001716058298335756193385156375561985521005550371049073877337319293242294814303804008282826692347790179420412343402088318836578088229730322866084747391,(-36207492201461862038513355769594626130566830514575012068805444082024694580137053035471992013326359075918186292781324696248438511863751187923880306284365),(-37842826835186649212920768710834989911338570372086054989510976861377416865829274355826216870606894800169043167253590687425463286387582226602287329921796)⟩

private theorem cell0 : Transports 464 465 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 464 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 465 466 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 465 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 466 467 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 466 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 467 468 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 467 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 468 469 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 468 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 469 470 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 469 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 470 471 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 470 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 471 472 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 471 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 472 473 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 472 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 473 474 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 473 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 474 475 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 474 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 475 476 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 475 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 476 477 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 476 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 477 478 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 477 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 478 479 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 478 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 479 480 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 479 _ _ (by decide) (by decide +kernel)

theorem negative_transport_464_480 : Transports 464 480 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_464_480
