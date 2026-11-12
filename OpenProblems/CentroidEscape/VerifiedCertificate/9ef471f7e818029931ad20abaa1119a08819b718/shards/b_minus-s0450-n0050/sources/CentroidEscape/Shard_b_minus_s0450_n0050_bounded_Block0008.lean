import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0490
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0491
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0492
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0493
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0494

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0491.inputData=Step0490.endpointData := by decide +kernel

theorem glue1 : Step0492.inputData=Step0491.endpointData := by decide +kernel

theorem glue2 : Step0493.inputData=Step0492.endpointData := by decide +kernel

theorem glue3 : Step0494.inputData=Step0493.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0490.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0494.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0490.stepData
  | 1=>Step0491.stepData
  | 2=>Step0492.stepData
  | 3=>Step0493.stepData
  | 4=>Step0494.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0490.stepData=true ∧
      (∀ i : Fin 7, Step0491.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0490.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0490.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0490.allStagesChecked,?_,Step0490.initialMarginCheck⟩
    intro i
    rw [Step0491.inputCoefficient,← Step0490.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0491.stepData=true ∧
      (∀ i : Fin 7, Step0492.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0491.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0491.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0491.allStagesChecked,?_,Step0491.initialMarginCheck⟩
    intro i
    rw [Step0492.inputCoefficient,← Step0491.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0492.stepData=true ∧
      (∀ i : Fin 7, Step0493.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0492.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0492.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0492.allStagesChecked,?_,Step0492.initialMarginCheck⟩
    intro i
    rw [Step0493.inputCoefficient,← Step0492.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0493.stepData=true ∧
      (∀ i : Fin 7, Step0494.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0493.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0493.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0493.allStagesChecked,?_,Step0493.initialMarginCheck⟩
    intro i
    rw [Step0494.inputCoefficient,← Step0493.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0494.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0494.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0494.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0494.allStagesChecked,?_,Step0494.initialMarginCheck⟩
    intro i
    change Step0494.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0494.stepData)[i.val]
    rw [← Step0494.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0490.stepData.coefficient 0 i=Step0490.inputData[i.val]
  exact Step0490.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0008
