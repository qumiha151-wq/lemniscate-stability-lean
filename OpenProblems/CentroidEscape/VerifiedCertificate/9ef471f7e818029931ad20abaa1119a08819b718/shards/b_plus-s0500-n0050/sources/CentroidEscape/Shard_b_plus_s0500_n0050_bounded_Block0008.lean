import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0540
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0541
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0542
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0543
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0544

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0541.inputData=Step0540.endpointData := by decide +kernel

theorem glue1 : Step0542.inputData=Step0541.endpointData := by decide +kernel

theorem glue2 : Step0543.inputData=Step0542.endpointData := by decide +kernel

theorem glue3 : Step0544.inputData=Step0543.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0540.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0544.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0540.stepData
  | 1=>Step0541.stepData
  | 2=>Step0542.stepData
  | 3=>Step0543.stepData
  | 4=>Step0544.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0540.stepData=true ∧
      (∀ i : Fin 7, Step0541.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0540.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0540.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0540.allStagesChecked,?_,Step0540.initialMarginCheck⟩
    intro i
    rw [Step0541.inputCoefficient,← Step0540.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0541.stepData=true ∧
      (∀ i : Fin 7, Step0542.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0541.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0541.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0541.allStagesChecked,?_,Step0541.initialMarginCheck⟩
    intro i
    rw [Step0542.inputCoefficient,← Step0541.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0542.stepData=true ∧
      (∀ i : Fin 7, Step0543.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0542.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0542.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0542.allStagesChecked,?_,Step0542.initialMarginCheck⟩
    intro i
    rw [Step0543.inputCoefficient,← Step0542.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0543.stepData=true ∧
      (∀ i : Fin 7, Step0544.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0543.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0543.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0543.allStagesChecked,?_,Step0543.initialMarginCheck⟩
    intro i
    rw [Step0544.inputCoefficient,← Step0543.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0544.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0544.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0544.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0544.allStagesChecked,?_,Step0544.initialMarginCheck⟩
    intro i
    change Step0544.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0544.stepData)[i.val]
    rw [← Step0544.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0540.stepData.coefficient 0 i=Step0540.inputData[i.val]
  exact Step0540.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Block0008
