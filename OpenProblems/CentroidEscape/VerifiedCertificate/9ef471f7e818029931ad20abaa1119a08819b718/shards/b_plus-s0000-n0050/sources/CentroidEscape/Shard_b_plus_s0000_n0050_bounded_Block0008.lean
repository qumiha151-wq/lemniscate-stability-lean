import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0040
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0041
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0042
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0043
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0044

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0041.inputData=Step0040.endpointData := by decide +kernel

theorem glue1 : Step0042.inputData=Step0041.endpointData := by decide +kernel

theorem glue2 : Step0043.inputData=Step0042.endpointData := by decide +kernel

theorem glue3 : Step0044.inputData=Step0043.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0040.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0044.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0040.stepData
  | 1=>Step0041.stepData
  | 2=>Step0042.stepData
  | 3=>Step0043.stepData
  | 4=>Step0044.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0040.stepData=true ∧
      (∀ i : Fin 7, Step0041.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0040.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0040.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0040.allStagesChecked,?_,Step0040.initialMarginCheck⟩
    intro i
    rw [Step0041.inputCoefficient,← Step0040.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0041.stepData=true ∧
      (∀ i : Fin 7, Step0042.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0041.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0041.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0041.allStagesChecked,?_,Step0041.initialMarginCheck⟩
    intro i
    rw [Step0042.inputCoefficient,← Step0041.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0042.stepData=true ∧
      (∀ i : Fin 7, Step0043.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0042.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0042.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0042.allStagesChecked,?_,Step0042.initialMarginCheck⟩
    intro i
    rw [Step0043.inputCoefficient,← Step0042.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0043.stepData=true ∧
      (∀ i : Fin 7, Step0044.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0043.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0043.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0043.allStagesChecked,?_,Step0043.initialMarginCheck⟩
    intro i
    rw [Step0044.inputCoefficient,← Step0043.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0044.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0044.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0044.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0044.allStagesChecked,?_,Step0044.initialMarginCheck⟩
    intro i
    change Step0044.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0044.stepData)[i.val]
    rw [← Step0044.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0040.stepData.coefficient 0 i=Step0040.inputData[i.val]
  exact Step0040.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Block0008
