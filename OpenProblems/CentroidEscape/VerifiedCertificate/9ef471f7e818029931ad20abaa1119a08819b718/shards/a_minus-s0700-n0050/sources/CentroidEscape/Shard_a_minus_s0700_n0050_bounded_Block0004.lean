import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0720
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0721
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0722
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0723
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0724

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0721.inputData=Step0720.endpointData := by decide +kernel

theorem glue1 : Step0722.inputData=Step0721.endpointData := by decide +kernel

theorem glue2 : Step0723.inputData=Step0722.endpointData := by decide +kernel

theorem glue3 : Step0724.inputData=Step0723.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0720.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0724.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0720.stepData
  | 1=>Step0721.stepData
  | 2=>Step0722.stepData
  | 3=>Step0723.stepData
  | 4=>Step0724.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0720.stepData=true ∧
      (∀ i : Fin 7, Step0721.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0720.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0720.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0720.allStagesChecked,?_,Step0720.initialMarginCheck⟩
    intro i
    rw [Step0721.inputCoefficient,← Step0720.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0721.stepData=true ∧
      (∀ i : Fin 7, Step0722.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0721.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0721.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0721.allStagesChecked,?_,Step0721.initialMarginCheck⟩
    intro i
    rw [Step0722.inputCoefficient,← Step0721.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0722.stepData=true ∧
      (∀ i : Fin 7, Step0723.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0722.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0722.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0722.allStagesChecked,?_,Step0722.initialMarginCheck⟩
    intro i
    rw [Step0723.inputCoefficient,← Step0722.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0723.stepData=true ∧
      (∀ i : Fin 7, Step0724.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0723.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0723.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0723.allStagesChecked,?_,Step0723.initialMarginCheck⟩
    intro i
    rw [Step0724.inputCoefficient,← Step0723.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0724.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0724.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0724.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0724.allStagesChecked,?_,Step0724.initialMarginCheck⟩
    intro i
    change Step0724.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0724.stepData)[i.val]
    rw [← Step0724.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0720.stepData.coefficient 0 i=Step0720.inputData[i.val]
  exact Step0720.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0004
