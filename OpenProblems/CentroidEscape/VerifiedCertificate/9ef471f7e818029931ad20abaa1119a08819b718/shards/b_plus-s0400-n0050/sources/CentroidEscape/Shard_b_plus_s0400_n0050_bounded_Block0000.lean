import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0400
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0401
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0402
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0403
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0404

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0401.inputData=Step0400.endpointData := by decide +kernel

theorem glue1 : Step0402.inputData=Step0401.endpointData := by decide +kernel

theorem glue2 : Step0403.inputData=Step0402.endpointData := by decide +kernel

theorem glue3 : Step0404.inputData=Step0403.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0400.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0404.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0400.stepData
  | 1=>Step0401.stepData
  | 2=>Step0402.stepData
  | 3=>Step0403.stepData
  | 4=>Step0404.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0400.stepData=true ∧
      (∀ i : Fin 7, Step0401.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0400.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0400.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0400.allStagesChecked,?_,Step0400.initialMarginCheck⟩
    intro i
    rw [Step0401.inputCoefficient,← Step0400.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0401.stepData=true ∧
      (∀ i : Fin 7, Step0402.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0401.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0401.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0401.allStagesChecked,?_,Step0401.initialMarginCheck⟩
    intro i
    rw [Step0402.inputCoefficient,← Step0401.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0402.stepData=true ∧
      (∀ i : Fin 7, Step0403.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0402.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0402.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0402.allStagesChecked,?_,Step0402.initialMarginCheck⟩
    intro i
    rw [Step0403.inputCoefficient,← Step0402.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0403.stepData=true ∧
      (∀ i : Fin 7, Step0404.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0403.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0403.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0403.allStagesChecked,?_,Step0403.initialMarginCheck⟩
    intro i
    rw [Step0404.inputCoefficient,← Step0403.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0404.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0404.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0404.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0404.allStagesChecked,?_,Step0404.initialMarginCheck⟩
    intro i
    change Step0404.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0404.stepData)[i.val]
    rw [← Step0404.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0400.stepData.coefficient 0 i=Step0400.inputData[i.val]
  exact Step0400.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0000
