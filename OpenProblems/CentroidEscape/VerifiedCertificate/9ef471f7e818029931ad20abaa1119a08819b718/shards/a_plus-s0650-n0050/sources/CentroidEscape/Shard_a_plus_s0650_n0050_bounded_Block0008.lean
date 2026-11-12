import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0690
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0691
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0692
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0693
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0694

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0691.inputData=Step0690.endpointData := by decide +kernel

theorem glue1 : Step0692.inputData=Step0691.endpointData := by decide +kernel

theorem glue2 : Step0693.inputData=Step0692.endpointData := by decide +kernel

theorem glue3 : Step0694.inputData=Step0693.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0690.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0694.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0690.stepData
  | 1=>Step0691.stepData
  | 2=>Step0692.stepData
  | 3=>Step0693.stepData
  | 4=>Step0694.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0690.stepData=true ∧
      (∀ i : Fin 7, Step0691.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0690.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0690.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0690.allStagesChecked,?_,Step0690.initialMarginCheck⟩
    intro i
    rw [Step0691.inputCoefficient,← Step0690.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0691.stepData=true ∧
      (∀ i : Fin 7, Step0692.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0691.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0691.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0691.allStagesChecked,?_,Step0691.initialMarginCheck⟩
    intro i
    rw [Step0692.inputCoefficient,← Step0691.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0692.stepData=true ∧
      (∀ i : Fin 7, Step0693.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0692.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0692.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0692.allStagesChecked,?_,Step0692.initialMarginCheck⟩
    intro i
    rw [Step0693.inputCoefficient,← Step0692.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0693.stepData=true ∧
      (∀ i : Fin 7, Step0694.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0693.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0693.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0693.allStagesChecked,?_,Step0693.initialMarginCheck⟩
    intro i
    rw [Step0694.inputCoefficient,← Step0693.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0694.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0694.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0694.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0694.allStagesChecked,?_,Step0694.initialMarginCheck⟩
    intro i
    change Step0694.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0694.stepData)[i.val]
    rw [← Step0694.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0690.stepData.coefficient 0 i=Step0690.inputData[i.val]
  exact Step0690.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Block0008
