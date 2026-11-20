import SolitonClassification.Reflected.PlusB000
import SolitonClassification.Reflected.PlusB020
import SolitonClassification.Reflected.PlusB040
import SolitonClassification.Reflected.PlusB060
import SolitonClassification.Reflected.PlusB080
import SolitonClassification.Reflected.PlusB100
import SolitonClassification.Reflected.PlusB120
import SolitonClassification.Reflected.PlusB140
import SolitonClassification.Reflected.PlusB160
import SolitonClassification.Reflected.PlusB180
import SolitonClassification.Reflected.PlusB200
import SolitonClassification.Reflected.PlusB220
import SolitonClassification.Reflected.PlusB240
import SolitonClassification.Reflected.PlusB260
import SolitonClassification.Reflected.PlusB280
import SolitonClassification.Reflected.PlusB300
import SolitonClassification.Reflected.PlusB320
import SolitonClassification.Reflected.PlusB340
import SolitonClassification.Reflected.PlusB360
import SolitonClassification.Reflected.PlusB380
import SolitonClassification.Reflected.PlusB400
import SolitonClassification.Reflected.PlusB420
import SolitonClassification.Reflected.PlusB440
import SolitonClassification.Reflected.PlusB460
import SolitonClassification.Reflected.PlusB480
import SolitonClassification.Reflected.PlusB500
import SolitonClassification.Reflected.PlusB520
import SolitonClassification.Reflected.PlusB540
import SolitonClassification.Reflected.PlusB560
import SolitonClassification.Reflected.PlusB580
import SolitonClassification.Reflected.PlusB600
import SolitonClassification.Reflected.PlusB620
import SolitonClassification.Reflected.PlusB640
import SolitonClassification.Reflected.PlusB660
import SolitonClassification.Reflected.PlusB680
import SolitonClassification.Reflected.PlusB700
import SolitonClassification.Reflected.PlusB720
namespace SolitonClassification.Reflected
namespace PlusTrajectory
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option linter.unnecessarySeqFocus false
theorem trajectory : Segment traceStep PlusB000.b0 PlusB720.b740 (740*(traceStep:ℝ)) := by
  convert (((((((((((((((((((((((((((((((((((((PlusB000.block).join PlusB020.block).join PlusB040.block).join PlusB060.block).join PlusB080.block).join PlusB100.block).join PlusB120.block).join PlusB140.block).join PlusB160.block).join PlusB180.block).join PlusB200.block).join PlusB220.block).join PlusB240.block).join PlusB260.block).join PlusB280.block).join PlusB300.block).join PlusB320.block).join PlusB340.block).join PlusB360.block).join PlusB380.block).join PlusB400.block).join PlusB420.block).join PlusB440.block).join PlusB460.block).join PlusB480.block).join PlusB500.block).join PlusB520.block).join PlusB540.block).join PlusB560.block).join PlusB580.block).join PlusB600.block).join PlusB620.block).join PlusB640.block).join PlusB660.block).join PlusB680.block).join PlusB700.block).join PlusB720.block) using 1 <;> ring
end PlusTrajectory
end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.PlusTrajectory.trajectory
