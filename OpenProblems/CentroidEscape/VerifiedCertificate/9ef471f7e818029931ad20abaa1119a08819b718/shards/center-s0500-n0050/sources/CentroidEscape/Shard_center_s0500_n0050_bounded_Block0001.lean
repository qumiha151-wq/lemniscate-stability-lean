import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0505
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0506
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0507
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0508
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0509

namespace CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0506.inputData=Step0505.endpointData := by decide +kernel

theorem glue1 : Step0507.inputData=Step0506.endpointData := by decide +kernel

theorem glue2 : Step0508.inputData=Step0507.endpointData := by decide +kernel

theorem glue3 : Step0509.inputData=Step0508.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0505.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0509.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0505.stepData
  | 1=>Step0506.stepData
  | 2=>Step0507.stepData
  | 3=>Step0508.stepData
  | 4=>Step0509.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0505.stepData=true ∧
      (∀ i : Fin 7, Step0506.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0505.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0505.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0505.allStagesChecked,?_,Step0505.initialMarginCheck⟩
    intro i
    rw [Step0506.inputCoefficient,← Step0505.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0506.stepData=true ∧
      (∀ i : Fin 7, Step0507.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0506.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0506.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0506.allStagesChecked,?_,Step0506.initialMarginCheck⟩
    intro i
    rw [Step0507.inputCoefficient,← Step0506.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0507.stepData=true ∧
      (∀ i : Fin 7, Step0508.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0507.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0507.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0507.allStagesChecked,?_,Step0507.initialMarginCheck⟩
    intro i
    rw [Step0508.inputCoefficient,← Step0507.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0508.stepData=true ∧
      (∀ i : Fin 7, Step0509.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0508.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0508.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0508.allStagesChecked,?_,Step0508.initialMarginCheck⟩
    intro i
    rw [Step0509.inputCoefficient,← Step0508.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0509.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0509.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0509.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0509.allStagesChecked,?_,Step0509.initialMarginCheck⟩
    intro i
    change Step0509.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0509.stepData)[i.val]
    rw [← Step0509.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0505.stepData.coefficient 0 i=Step0505.inputData[i.val]
  exact Step0505.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Block0001
