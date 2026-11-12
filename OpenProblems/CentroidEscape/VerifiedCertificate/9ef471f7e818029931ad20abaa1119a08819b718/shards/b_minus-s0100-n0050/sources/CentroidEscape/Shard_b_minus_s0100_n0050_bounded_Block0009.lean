import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0145
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0146
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0147
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0148
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0149

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0146.inputData=Step0145.endpointData := by decide +kernel

theorem glue1 : Step0147.inputData=Step0146.endpointData := by decide +kernel

theorem glue2 : Step0148.inputData=Step0147.endpointData := by decide +kernel

theorem glue3 : Step0149.inputData=Step0148.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0145.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0149.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0145.stepData
  | 1=>Step0146.stepData
  | 2=>Step0147.stepData
  | 3=>Step0148.stepData
  | 4=>Step0149.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0145.stepData=true ∧
      (∀ i : Fin 7, Step0146.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0145.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0145.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0145.allStagesChecked,?_,Step0145.initialMarginCheck⟩
    intro i
    rw [Step0146.inputCoefficient,← Step0145.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0146.stepData=true ∧
      (∀ i : Fin 7, Step0147.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0146.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0146.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0146.allStagesChecked,?_,Step0146.initialMarginCheck⟩
    intro i
    rw [Step0147.inputCoefficient,← Step0146.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0147.stepData=true ∧
      (∀ i : Fin 7, Step0148.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0147.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0147.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0147.allStagesChecked,?_,Step0147.initialMarginCheck⟩
    intro i
    rw [Step0148.inputCoefficient,← Step0147.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0148.stepData=true ∧
      (∀ i : Fin 7, Step0149.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0148.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0148.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0148.allStagesChecked,?_,Step0148.initialMarginCheck⟩
    intro i
    rw [Step0149.inputCoefficient,← Step0148.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0149.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0149.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0149.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0149.allStagesChecked,?_,Step0149.initialMarginCheck⟩
    intro i
    change Step0149.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0149.stepData)[i.val]
    rw [← Step0149.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0145.stepData.coefficient 0 i=Step0145.inputData[i.val]
  exact Step0145.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Block0009
