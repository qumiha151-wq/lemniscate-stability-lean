import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0060
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0061
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0062
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0063
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0064

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0050_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0061.inputData=Step0060.endpointData := by decide +kernel

theorem glue1 : Step0062.inputData=Step0061.endpointData := by decide +kernel

theorem glue2 : Step0063.inputData=Step0062.endpointData := by decide +kernel

theorem glue3 : Step0064.inputData=Step0063.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0060.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0064.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0060.stepData
  | 1=>Step0061.stepData
  | 2=>Step0062.stepData
  | 3=>Step0063.stepData
  | 4=>Step0064.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0060.stepData=true ∧
      (∀ i : Fin 7, Step0061.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0060.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0060.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0060.allStagesChecked,?_,Step0060.initialMarginCheck⟩
    intro i
    rw [Step0061.inputCoefficient,← Step0060.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0061.stepData=true ∧
      (∀ i : Fin 7, Step0062.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0061.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0061.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0061.allStagesChecked,?_,Step0061.initialMarginCheck⟩
    intro i
    rw [Step0062.inputCoefficient,← Step0061.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0062.stepData=true ∧
      (∀ i : Fin 7, Step0063.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0062.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0062.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0062.allStagesChecked,?_,Step0062.initialMarginCheck⟩
    intro i
    rw [Step0063.inputCoefficient,← Step0062.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0063.stepData=true ∧
      (∀ i : Fin 7, Step0064.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0063.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0063.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0063.allStagesChecked,?_,Step0063.initialMarginCheck⟩
    intro i
    rw [Step0064.inputCoefficient,← Step0063.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0064.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0064.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0064.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0064.allStagesChecked,?_,Step0064.initialMarginCheck⟩
    intro i
    change Step0064.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0064.stepData)[i.val]
    rw [← Step0064.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0060.stepData.coefficient 0 i=Step0060.inputData[i.val]
  exact Step0060.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0050_n0050_bounded.Block0002
