import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0655
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0656
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0657
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0658
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0659

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0656.inputData=Step0655.endpointData := by decide +kernel

theorem glue1 : Step0657.inputData=Step0656.endpointData := by decide +kernel

theorem glue2 : Step0658.inputData=Step0657.endpointData := by decide +kernel

theorem glue3 : Step0659.inputData=Step0658.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0655.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0659.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0655.stepData
  | 1=>Step0656.stepData
  | 2=>Step0657.stepData
  | 3=>Step0658.stepData
  | 4=>Step0659.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0655.stepData=true ∧
      (∀ i : Fin 7, Step0656.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0655.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0655.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0655.allStagesChecked,?_,Step0655.initialMarginCheck⟩
    intro i
    rw [Step0656.inputCoefficient,← Step0655.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0656.stepData=true ∧
      (∀ i : Fin 7, Step0657.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0656.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0656.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0656.allStagesChecked,?_,Step0656.initialMarginCheck⟩
    intro i
    rw [Step0657.inputCoefficient,← Step0656.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0657.stepData=true ∧
      (∀ i : Fin 7, Step0658.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0657.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0657.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0657.allStagesChecked,?_,Step0657.initialMarginCheck⟩
    intro i
    rw [Step0658.inputCoefficient,← Step0657.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0658.stepData=true ∧
      (∀ i : Fin 7, Step0659.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0658.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0658.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0658.allStagesChecked,?_,Step0658.initialMarginCheck⟩
    intro i
    rw [Step0659.inputCoefficient,← Step0658.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0659.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0659.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0659.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0659.allStagesChecked,?_,Step0659.initialMarginCheck⟩
    intro i
    change Step0659.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0659.stepData)[i.val]
    rw [← Step0659.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0655.stepData.coefficient 0 i=Step0655.inputData[i.val]
  exact Step0655.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Block0001
