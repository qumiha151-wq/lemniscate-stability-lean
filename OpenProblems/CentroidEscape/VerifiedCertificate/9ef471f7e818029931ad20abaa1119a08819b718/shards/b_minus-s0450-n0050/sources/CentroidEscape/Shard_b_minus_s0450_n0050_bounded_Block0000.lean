import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0450
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0451
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0452
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0453
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0454

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0451.inputData=Step0450.endpointData := by decide +kernel

theorem glue1 : Step0452.inputData=Step0451.endpointData := by decide +kernel

theorem glue2 : Step0453.inputData=Step0452.endpointData := by decide +kernel

theorem glue3 : Step0454.inputData=Step0453.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0450.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0454.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0450.stepData
  | 1=>Step0451.stepData
  | 2=>Step0452.stepData
  | 3=>Step0453.stepData
  | 4=>Step0454.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0450.stepData=true ∧
      (∀ i : Fin 7, Step0451.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0450.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0450.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0450.allStagesChecked,?_,Step0450.initialMarginCheck⟩
    intro i
    rw [Step0451.inputCoefficient,← Step0450.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0451.stepData=true ∧
      (∀ i : Fin 7, Step0452.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0451.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0451.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0451.allStagesChecked,?_,Step0451.initialMarginCheck⟩
    intro i
    rw [Step0452.inputCoefficient,← Step0451.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0452.stepData=true ∧
      (∀ i : Fin 7, Step0453.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0452.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0452.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0452.allStagesChecked,?_,Step0452.initialMarginCheck⟩
    intro i
    rw [Step0453.inputCoefficient,← Step0452.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0453.stepData=true ∧
      (∀ i : Fin 7, Step0454.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0453.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0453.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0453.allStagesChecked,?_,Step0453.initialMarginCheck⟩
    intro i
    rw [Step0454.inputCoefficient,← Step0453.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0454.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0454.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0454.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0454.allStagesChecked,?_,Step0454.initialMarginCheck⟩
    intro i
    change Step0454.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0454.stepData)[i.val]
    rw [← Step0454.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0450.stepData.coefficient 0 i=Step0450.inputData[i.val]
  exact Step0450.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0000
