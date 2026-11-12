import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0340
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0341
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0342
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0343
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0344

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0341.inputData=Step0340.endpointData := by decide +kernel

theorem glue1 : Step0342.inputData=Step0341.endpointData := by decide +kernel

theorem glue2 : Step0343.inputData=Step0342.endpointData := by decide +kernel

theorem glue3 : Step0344.inputData=Step0343.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0340.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0344.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0340.stepData
  | 1=>Step0341.stepData
  | 2=>Step0342.stepData
  | 3=>Step0343.stepData
  | 4=>Step0344.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0340.stepData=true ∧
      (∀ i : Fin 7, Step0341.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0340.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0340.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0340.allStagesChecked,?_,Step0340.initialMarginCheck⟩
    intro i
    rw [Step0341.inputCoefficient,← Step0340.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0341.stepData=true ∧
      (∀ i : Fin 7, Step0342.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0341.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0341.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0341.allStagesChecked,?_,Step0341.initialMarginCheck⟩
    intro i
    rw [Step0342.inputCoefficient,← Step0341.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0342.stepData=true ∧
      (∀ i : Fin 7, Step0343.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0342.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0342.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0342.allStagesChecked,?_,Step0342.initialMarginCheck⟩
    intro i
    rw [Step0343.inputCoefficient,← Step0342.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0343.stepData=true ∧
      (∀ i : Fin 7, Step0344.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0343.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0343.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0343.allStagesChecked,?_,Step0343.initialMarginCheck⟩
    intro i
    rw [Step0344.inputCoefficient,← Step0343.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0344.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0344.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0344.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0344.allStagesChecked,?_,Step0344.initialMarginCheck⟩
    intro i
    change Step0344.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0344.stepData)[i.val]
    rw [← Step0344.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0340.stepData.coefficient 0 i=Step0340.inputData[i.val]
  exact Step0340.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Block0008
