import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0100
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0101
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0102
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0103
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0104

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0101.inputData=Step0100.endpointData := by decide +kernel

theorem glue1 : Step0102.inputData=Step0101.endpointData := by decide +kernel

theorem glue2 : Step0103.inputData=Step0102.endpointData := by decide +kernel

theorem glue3 : Step0104.inputData=Step0103.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0100.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0104.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0100.stepData
  | 1=>Step0101.stepData
  | 2=>Step0102.stepData
  | 3=>Step0103.stepData
  | 4=>Step0104.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0100.stepData=true ∧
      (∀ i : Fin 7, Step0101.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0100.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0100.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0100.allStagesChecked,?_,Step0100.initialMarginCheck⟩
    intro i
    rw [Step0101.inputCoefficient,← Step0100.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0101.stepData=true ∧
      (∀ i : Fin 7, Step0102.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0101.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0101.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0101.allStagesChecked,?_,Step0101.initialMarginCheck⟩
    intro i
    rw [Step0102.inputCoefficient,← Step0101.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0102.stepData=true ∧
      (∀ i : Fin 7, Step0103.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0102.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0102.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0102.allStagesChecked,?_,Step0102.initialMarginCheck⟩
    intro i
    rw [Step0103.inputCoefficient,← Step0102.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0103.stepData=true ∧
      (∀ i : Fin 7, Step0104.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0103.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0103.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0103.allStagesChecked,?_,Step0103.initialMarginCheck⟩
    intro i
    rw [Step0104.inputCoefficient,← Step0103.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0104.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0104.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0104.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0104.allStagesChecked,?_,Step0104.initialMarginCheck⟩
    intro i
    change Step0104.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0104.stepData)[i.val]
    rw [← Step0104.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0100.stepData.coefficient 0 i=Step0100.inputData[i.val]
  exact Step0100.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Block0000
