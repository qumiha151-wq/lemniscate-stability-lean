import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0210
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0211
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0212
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0213
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0214

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0211.inputData=Step0210.endpointData := by decide +kernel

theorem glue1 : Step0212.inputData=Step0211.endpointData := by decide +kernel

theorem glue2 : Step0213.inputData=Step0212.endpointData := by decide +kernel

theorem glue3 : Step0214.inputData=Step0213.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0210.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0214.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0210.stepData
  | 1=>Step0211.stepData
  | 2=>Step0212.stepData
  | 3=>Step0213.stepData
  | 4=>Step0214.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0210.stepData=true ∧
      (∀ i : Fin 7, Step0211.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0210.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0210.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0210.allStagesChecked,?_,Step0210.initialMarginCheck⟩
    intro i
    rw [Step0211.inputCoefficient,← Step0210.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0211.stepData=true ∧
      (∀ i : Fin 7, Step0212.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0211.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0211.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0211.allStagesChecked,?_,Step0211.initialMarginCheck⟩
    intro i
    rw [Step0212.inputCoefficient,← Step0211.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0212.stepData=true ∧
      (∀ i : Fin 7, Step0213.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0212.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0212.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0212.allStagesChecked,?_,Step0212.initialMarginCheck⟩
    intro i
    rw [Step0213.inputCoefficient,← Step0212.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0213.stepData=true ∧
      (∀ i : Fin 7, Step0214.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0213.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0213.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0213.allStagesChecked,?_,Step0213.initialMarginCheck⟩
    intro i
    rw [Step0214.inputCoefficient,← Step0213.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0214.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0214.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0214.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0214.allStagesChecked,?_,Step0214.initialMarginCheck⟩
    intro i
    change Step0214.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0214.stepData)[i.val]
    rw [← Step0214.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0210.stepData.coefficient 0 i=Step0210.inputData[i.val]
  exact Step0210.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0002
