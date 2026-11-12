import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0675
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0676
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0677
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0678
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0679

namespace CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0676.inputData=Step0675.endpointData := by decide +kernel

theorem glue1 : Step0677.inputData=Step0676.endpointData := by decide +kernel

theorem glue2 : Step0678.inputData=Step0677.endpointData := by decide +kernel

theorem glue3 : Step0679.inputData=Step0678.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0675.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0679.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0675.stepData
  | 1=>Step0676.stepData
  | 2=>Step0677.stepData
  | 3=>Step0678.stepData
  | 4=>Step0679.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0675.stepData=true ∧
      (∀ i : Fin 7, Step0676.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0675.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0675.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0675.allStagesChecked,?_,Step0675.initialMarginCheck⟩
    intro i
    rw [Step0676.inputCoefficient,← Step0675.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0676.stepData=true ∧
      (∀ i : Fin 7, Step0677.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0676.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0676.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0676.allStagesChecked,?_,Step0676.initialMarginCheck⟩
    intro i
    rw [Step0677.inputCoefficient,← Step0676.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0677.stepData=true ∧
      (∀ i : Fin 7, Step0678.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0677.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0677.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0677.allStagesChecked,?_,Step0677.initialMarginCheck⟩
    intro i
    rw [Step0678.inputCoefficient,← Step0677.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0678.stepData=true ∧
      (∀ i : Fin 7, Step0679.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0678.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0678.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0678.allStagesChecked,?_,Step0678.initialMarginCheck⟩
    intro i
    rw [Step0679.inputCoefficient,← Step0678.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0679.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0679.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0679.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0679.allStagesChecked,?_,Step0679.initialMarginCheck⟩
    intro i
    change Step0679.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0679.stepData)[i.val]
    rw [← Step0679.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0675.stepData.coefficient 0 i=Step0675.inputData[i.val]
  exact Step0675.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Block0005
