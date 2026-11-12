import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0615
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0616
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0617
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0618
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0619

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0616.inputData=Step0615.endpointData := by decide +kernel

theorem glue1 : Step0617.inputData=Step0616.endpointData := by decide +kernel

theorem glue2 : Step0618.inputData=Step0617.endpointData := by decide +kernel

theorem glue3 : Step0619.inputData=Step0618.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0615.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0619.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0615.stepData
  | 1=>Step0616.stepData
  | 2=>Step0617.stepData
  | 3=>Step0618.stepData
  | 4=>Step0619.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0615.stepData=true ∧
      (∀ i : Fin 7, Step0616.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0615.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0615.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0615.allStagesChecked,?_,Step0615.initialMarginCheck⟩
    intro i
    rw [Step0616.inputCoefficient,← Step0615.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0616.stepData=true ∧
      (∀ i : Fin 7, Step0617.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0616.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0616.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0616.allStagesChecked,?_,Step0616.initialMarginCheck⟩
    intro i
    rw [Step0617.inputCoefficient,← Step0616.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0617.stepData=true ∧
      (∀ i : Fin 7, Step0618.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0617.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0617.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0617.allStagesChecked,?_,Step0617.initialMarginCheck⟩
    intro i
    rw [Step0618.inputCoefficient,← Step0617.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0618.stepData=true ∧
      (∀ i : Fin 7, Step0619.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0618.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0618.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0618.allStagesChecked,?_,Step0618.initialMarginCheck⟩
    intro i
    rw [Step0619.inputCoefficient,← Step0618.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0619.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0619.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0619.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0619.allStagesChecked,?_,Step0619.initialMarginCheck⟩
    intro i
    change Step0619.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0619.stepData)[i.val]
    rw [← Step0619.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0615.stepData.coefficient 0 i=Step0615.inputData[i.val]
  exact Step0615.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Block0003
