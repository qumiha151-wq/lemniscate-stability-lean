import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0550_n0050_bounded_Step0595
import CentroidEscape.Shard_center_s0550_n0050_bounded_Step0596
import CentroidEscape.Shard_center_s0550_n0050_bounded_Step0597
import CentroidEscape.Shard_center_s0550_n0050_bounded_Step0598
import CentroidEscape.Shard_center_s0550_n0050_bounded_Step0599

namespace CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0596.inputData=Step0595.endpointData := by decide +kernel

theorem glue1 : Step0597.inputData=Step0596.endpointData := by decide +kernel

theorem glue2 : Step0598.inputData=Step0597.endpointData := by decide +kernel

theorem glue3 : Step0599.inputData=Step0598.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0595.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0599.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0595.stepData
  | 1=>Step0596.stepData
  | 2=>Step0597.stepData
  | 3=>Step0598.stepData
  | 4=>Step0599.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0595.stepData=true ∧
      (∀ i : Fin 7, Step0596.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0595.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0595.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0595.allStagesChecked,?_,Step0595.initialMarginCheck⟩
    intro i
    rw [Step0596.inputCoefficient,← Step0595.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0596.stepData=true ∧
      (∀ i : Fin 7, Step0597.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0596.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0596.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0596.allStagesChecked,?_,Step0596.initialMarginCheck⟩
    intro i
    rw [Step0597.inputCoefficient,← Step0596.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0597.stepData=true ∧
      (∀ i : Fin 7, Step0598.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0597.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0597.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0597.allStagesChecked,?_,Step0597.initialMarginCheck⟩
    intro i
    rw [Step0598.inputCoefficient,← Step0597.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0598.stepData=true ∧
      (∀ i : Fin 7, Step0599.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0598.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0598.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0598.allStagesChecked,?_,Step0598.initialMarginCheck⟩
    intro i
    rw [Step0599.inputCoefficient,← Step0598.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0599.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0599.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0599.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0599.allStagesChecked,?_,Step0599.initialMarginCheck⟩
    intro i
    change Step0599.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0599.stepData)[i.val]
    rw [← Step0599.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0595.stepData.coefficient 0 i=Step0595.inputData[i.val]
  exact Step0595.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Block0009
