import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0110
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0111
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0112
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0113
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Step0114

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0111.inputData=Step0110.endpointData := by decide +kernel

theorem glue1 : Step0112.inputData=Step0111.endpointData := by decide +kernel

theorem glue2 : Step0113.inputData=Step0112.endpointData := by decide +kernel

theorem glue3 : Step0114.inputData=Step0113.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0110.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0114.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0110.stepData
  | 1=>Step0111.stepData
  | 2=>Step0112.stepData
  | 3=>Step0113.stepData
  | 4=>Step0114.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0110.stepData=true ∧
      (∀ i : Fin 7, Step0111.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0110.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0110.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0110.allStagesChecked,?_,Step0110.initialMarginCheck⟩
    intro i
    rw [Step0111.inputCoefficient,← Step0110.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0111.stepData=true ∧
      (∀ i : Fin 7, Step0112.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0111.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0111.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0111.allStagesChecked,?_,Step0111.initialMarginCheck⟩
    intro i
    rw [Step0112.inputCoefficient,← Step0111.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0112.stepData=true ∧
      (∀ i : Fin 7, Step0113.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0112.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0112.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0112.allStagesChecked,?_,Step0112.initialMarginCheck⟩
    intro i
    rw [Step0113.inputCoefficient,← Step0112.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0113.stepData=true ∧
      (∀ i : Fin 7, Step0114.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0113.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0113.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0113.allStagesChecked,?_,Step0113.initialMarginCheck⟩
    intro i
    rw [Step0114.inputCoefficient,← Step0113.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0114.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0114.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0114.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0114.allStagesChecked,?_,Step0114.initialMarginCheck⟩
    intro i
    change Step0114.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0114.stepData)[i.val]
    rw [← Step0114.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0110.stepData.coefficient 0 i=Step0110.inputData[i.val]
  exact Step0110.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Block0002
