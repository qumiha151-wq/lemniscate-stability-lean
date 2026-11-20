import SolitonClassification.Reflected.AllB000
import SolitonClassification.Reflected.AllB020
import SolitonClassification.Reflected.AllB040
import SolitonClassification.Reflected.AllB060
import SolitonClassification.Reflected.AllB080
import SolitonClassification.Reflected.AllB100
import SolitonClassification.Reflected.AllB120
import SolitonClassification.Reflected.AllB140
import SolitonClassification.Reflected.AllB160
import SolitonClassification.Reflected.AllB180
import SolitonClassification.Reflected.AllB200
import SolitonClassification.Reflected.AllB220
import SolitonClassification.Reflected.AllB240
import SolitonClassification.Reflected.AllB260
import SolitonClassification.Reflected.AllB280
import SolitonClassification.Reflected.AllB300
import SolitonClassification.Reflected.AllB320
import SolitonClassification.Reflected.AllB340
import SolitonClassification.Reflected.AllB360
import SolitonClassification.Reflected.AllB380
import SolitonClassification.Reflected.AllB400
import SolitonClassification.Reflected.AllB420
import SolitonClassification.Reflected.AllB440
import SolitonClassification.Reflected.AllB460
import SolitonClassification.Reflected.AllB480
import SolitonClassification.Reflected.AllB500
import SolitonClassification.Reflected.AllB520
import SolitonClassification.Reflected.AllB540
import SolitonClassification.Reflected.AllB560
import SolitonClassification.Reflected.AllB580
import SolitonClassification.Reflected.AllB600
import SolitonClassification.Reflected.AllB620
import SolitonClassification.Reflected.AllB640
import SolitonClassification.Reflected.AllB660
import SolitonClassification.Reflected.AllB680
import SolitonClassification.Reflected.AllB700
import SolitonClassification.Reflected.AllB720
namespace SolitonClassification.Reflected
namespace AllTrajectory
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option linter.unnecessarySeqFocus false
theorem trajectory : Segment traceStep AllB000.b0 AllB720.b740 (740*(traceStep:ℝ)) := by
  convert (((((((((((((((((((((((((((((((((((((AllB000.block).join AllB020.block).join AllB040.block).join AllB060.block).join AllB080.block).join AllB100.block).join AllB120.block).join AllB140.block).join AllB160.block).join AllB180.block).join AllB200.block).join AllB220.block).join AllB240.block).join AllB260.block).join AllB280.block).join AllB300.block).join AllB320.block).join AllB340.block).join AllB360.block).join AllB380.block).join AllB400.block).join AllB420.block).join AllB440.block).join AllB460.block).join AllB480.block).join AllB500.block).join AllB520.block).join AllB540.block).join AllB560.block).join AllB580.block).join AllB600.block).join AllB620.block).join AllB640.block).join AllB660.block).join AllB680.block).join AllB700.block).join AllB720.block) using 1 <;> ring
end AllTrajectory
end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.AllTrajectory.trajectory
