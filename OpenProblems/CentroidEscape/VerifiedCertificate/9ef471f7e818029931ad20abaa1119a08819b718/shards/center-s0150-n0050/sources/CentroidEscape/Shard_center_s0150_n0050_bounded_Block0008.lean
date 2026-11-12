import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0190
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0191
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0192
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0193
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0194

namespace CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0191.inputData=Step0190.endpointData := by decide +kernel

theorem glue1 : Step0192.inputData=Step0191.endpointData := by decide +kernel

theorem glue2 : Step0193.inputData=Step0192.endpointData := by decide +kernel

theorem glue3 : Step0194.inputData=Step0193.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0190.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0194.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0190.stepData
  | 1=>Step0191.stepData
  | 2=>Step0192.stepData
  | 3=>Step0193.stepData
  | 4=>Step0194.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0190.stepData=true ∧
      (∀ i : Fin 7, Step0191.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0190.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0190.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0190.allStagesChecked,?_,Step0190.initialMarginCheck⟩
    intro i
    rw [Step0191.inputCoefficient,← Step0190.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0191.stepData=true ∧
      (∀ i : Fin 7, Step0192.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0191.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0191.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0191.allStagesChecked,?_,Step0191.initialMarginCheck⟩
    intro i
    rw [Step0192.inputCoefficient,← Step0191.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0192.stepData=true ∧
      (∀ i : Fin 7, Step0193.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0192.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0192.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0192.allStagesChecked,?_,Step0192.initialMarginCheck⟩
    intro i
    rw [Step0193.inputCoefficient,← Step0192.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0193.stepData=true ∧
      (∀ i : Fin 7, Step0194.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0193.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0193.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0193.allStagesChecked,?_,Step0193.initialMarginCheck⟩
    intro i
    rw [Step0194.inputCoefficient,← Step0193.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0194.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0194.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0194.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0194.allStagesChecked,?_,Step0194.initialMarginCheck⟩
    intro i
    change Step0194.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0194.stepData)[i.val]
    rw [← Step0194.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0190.stepData.coefficient 0 i=Step0190.inputData[i.val]
  exact Step0190.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0008
