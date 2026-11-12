import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0345
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0346
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0347
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0348
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0349

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0346.inputData=Step0345.endpointData := by decide +kernel

theorem glue1 : Step0347.inputData=Step0346.endpointData := by decide +kernel

theorem glue2 : Step0348.inputData=Step0347.endpointData := by decide +kernel

theorem glue3 : Step0349.inputData=Step0348.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0345.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0349.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0345.stepData
  | 1=>Step0346.stepData
  | 2=>Step0347.stepData
  | 3=>Step0348.stepData
  | 4=>Step0349.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0345.stepData=true ∧
      (∀ i : Fin 7, Step0346.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0345.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0345.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0345.allStagesChecked,?_,Step0345.initialMarginCheck⟩
    intro i
    rw [Step0346.inputCoefficient,← Step0345.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0346.stepData=true ∧
      (∀ i : Fin 7, Step0347.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0346.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0346.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0346.allStagesChecked,?_,Step0346.initialMarginCheck⟩
    intro i
    rw [Step0347.inputCoefficient,← Step0346.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0347.stepData=true ∧
      (∀ i : Fin 7, Step0348.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0347.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0347.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0347.allStagesChecked,?_,Step0347.initialMarginCheck⟩
    intro i
    rw [Step0348.inputCoefficient,← Step0347.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0348.stepData=true ∧
      (∀ i : Fin 7, Step0349.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0348.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0348.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0348.allStagesChecked,?_,Step0348.initialMarginCheck⟩
    intro i
    rw [Step0349.inputCoefficient,← Step0348.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0349.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0349.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0349.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0349.allStagesChecked,?_,Step0349.initialMarginCheck⟩
    intro i
    change Step0349.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0349.stepData)[i.val]
    rw [← Step0349.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0345.stepData.coefficient 0 i=Step0345.inputData[i.val]
  exact Step0345.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Block0009
