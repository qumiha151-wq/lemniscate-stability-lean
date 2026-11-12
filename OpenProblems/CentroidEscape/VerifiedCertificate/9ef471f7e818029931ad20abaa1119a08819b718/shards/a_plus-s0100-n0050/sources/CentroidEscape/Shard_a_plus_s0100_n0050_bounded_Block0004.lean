import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0100_n0050_bounded_Step0120
import CentroidEscape.Shard_a_plus_s0100_n0050_bounded_Step0121
import CentroidEscape.Shard_a_plus_s0100_n0050_bounded_Step0122
import CentroidEscape.Shard_a_plus_s0100_n0050_bounded_Step0123
import CentroidEscape.Shard_a_plus_s0100_n0050_bounded_Step0124

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0100_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0121.inputData=Step0120.endpointData := by decide +kernel

theorem glue1 : Step0122.inputData=Step0121.endpointData := by decide +kernel

theorem glue2 : Step0123.inputData=Step0122.endpointData := by decide +kernel

theorem glue3 : Step0124.inputData=Step0123.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0120.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0124.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0120.stepData
  | 1=>Step0121.stepData
  | 2=>Step0122.stepData
  | 3=>Step0123.stepData
  | 4=>Step0124.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0120.stepData=true ∧
      (∀ i : Fin 7, Step0121.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0120.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0120.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0120.allStagesChecked,?_,Step0120.initialMarginCheck⟩
    intro i
    rw [Step0121.inputCoefficient,← Step0120.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0121.stepData=true ∧
      (∀ i : Fin 7, Step0122.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0121.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0121.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0121.allStagesChecked,?_,Step0121.initialMarginCheck⟩
    intro i
    rw [Step0122.inputCoefficient,← Step0121.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0122.stepData=true ∧
      (∀ i : Fin 7, Step0123.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0122.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0122.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0122.allStagesChecked,?_,Step0122.initialMarginCheck⟩
    intro i
    rw [Step0123.inputCoefficient,← Step0122.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0123.stepData=true ∧
      (∀ i : Fin 7, Step0124.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0123.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0123.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0123.allStagesChecked,?_,Step0123.initialMarginCheck⟩
    intro i
    rw [Step0124.inputCoefficient,← Step0123.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0124.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0124.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0124.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0124.allStagesChecked,?_,Step0124.initialMarginCheck⟩
    intro i
    change Step0124.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0124.stepData)[i.val]
    rw [← Step0124.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0120.stepData.coefficient 0 i=Step0120.inputData[i.val]
  exact Step0120.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0100_n0050_bounded.Block0004
