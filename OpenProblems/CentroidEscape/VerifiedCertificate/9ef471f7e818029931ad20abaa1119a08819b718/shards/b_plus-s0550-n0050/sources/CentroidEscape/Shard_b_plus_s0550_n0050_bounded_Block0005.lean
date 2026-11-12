import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0575
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0576
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0577
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0578
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0579

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0576.inputData=Step0575.endpointData := by decide +kernel

theorem glue1 : Step0577.inputData=Step0576.endpointData := by decide +kernel

theorem glue2 : Step0578.inputData=Step0577.endpointData := by decide +kernel

theorem glue3 : Step0579.inputData=Step0578.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0575.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0579.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0575.stepData
  | 1=>Step0576.stepData
  | 2=>Step0577.stepData
  | 3=>Step0578.stepData
  | 4=>Step0579.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0575.stepData=true ∧
      (∀ i : Fin 7, Step0576.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0575.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0575.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0575.allStagesChecked,?_,Step0575.initialMarginCheck⟩
    intro i
    rw [Step0576.inputCoefficient,← Step0575.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0576.stepData=true ∧
      (∀ i : Fin 7, Step0577.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0576.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0576.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0576.allStagesChecked,?_,Step0576.initialMarginCheck⟩
    intro i
    rw [Step0577.inputCoefficient,← Step0576.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0577.stepData=true ∧
      (∀ i : Fin 7, Step0578.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0577.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0577.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0577.allStagesChecked,?_,Step0577.initialMarginCheck⟩
    intro i
    rw [Step0578.inputCoefficient,← Step0577.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0578.stepData=true ∧
      (∀ i : Fin 7, Step0579.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0578.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0578.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0578.allStagesChecked,?_,Step0578.initialMarginCheck⟩
    intro i
    rw [Step0579.inputCoefficient,← Step0578.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0579.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0579.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0579.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0579.allStagesChecked,?_,Step0579.initialMarginCheck⟩
    intro i
    change Step0579.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0579.stepData)[i.val]
    rw [← Step0579.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0575.stepData.coefficient 0 i=Step0575.inputData[i.val]
  exact Step0575.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Block0005
