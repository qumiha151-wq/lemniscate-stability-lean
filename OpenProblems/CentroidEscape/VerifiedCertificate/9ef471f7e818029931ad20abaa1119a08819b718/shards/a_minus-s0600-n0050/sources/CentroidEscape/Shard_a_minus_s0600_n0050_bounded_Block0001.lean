import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0605
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0606
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0607
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0608
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0609

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0606.inputData=Step0605.endpointData := by decide +kernel

theorem glue1 : Step0607.inputData=Step0606.endpointData := by decide +kernel

theorem glue2 : Step0608.inputData=Step0607.endpointData := by decide +kernel

theorem glue3 : Step0609.inputData=Step0608.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0605.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0609.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0605.stepData
  | 1=>Step0606.stepData
  | 2=>Step0607.stepData
  | 3=>Step0608.stepData
  | 4=>Step0609.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0605.stepData=true ∧
      (∀ i : Fin 7, Step0606.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0605.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0605.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0605.allStagesChecked,?_,Step0605.initialMarginCheck⟩
    intro i
    rw [Step0606.inputCoefficient,← Step0605.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0606.stepData=true ∧
      (∀ i : Fin 7, Step0607.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0606.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0606.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0606.allStagesChecked,?_,Step0606.initialMarginCheck⟩
    intro i
    rw [Step0607.inputCoefficient,← Step0606.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0607.stepData=true ∧
      (∀ i : Fin 7, Step0608.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0607.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0607.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0607.allStagesChecked,?_,Step0607.initialMarginCheck⟩
    intro i
    rw [Step0608.inputCoefficient,← Step0607.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0608.stepData=true ∧
      (∀ i : Fin 7, Step0609.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0608.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0608.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0608.allStagesChecked,?_,Step0608.initialMarginCheck⟩
    intro i
    rw [Step0609.inputCoefficient,← Step0608.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0609.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0609.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0609.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0609.allStagesChecked,?_,Step0609.initialMarginCheck⟩
    intro i
    change Step0609.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0609.stepData)[i.val]
    rw [← Step0609.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0605.stepData.coefficient 0 i=Step0605.inputData[i.val]
  exact Step0605.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0001
