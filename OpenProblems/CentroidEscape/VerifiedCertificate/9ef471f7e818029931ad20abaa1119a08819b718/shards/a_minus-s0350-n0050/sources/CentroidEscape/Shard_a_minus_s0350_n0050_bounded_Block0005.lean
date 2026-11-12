import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0350_n0050_bounded_Step0375
import CentroidEscape.Shard_a_minus_s0350_n0050_bounded_Step0376
import CentroidEscape.Shard_a_minus_s0350_n0050_bounded_Step0377
import CentroidEscape.Shard_a_minus_s0350_n0050_bounded_Step0378
import CentroidEscape.Shard_a_minus_s0350_n0050_bounded_Step0379

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0376.inputData=Step0375.endpointData := by decide +kernel

theorem glue1 : Step0377.inputData=Step0376.endpointData := by decide +kernel

theorem glue2 : Step0378.inputData=Step0377.endpointData := by decide +kernel

theorem glue3 : Step0379.inputData=Step0378.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0375.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0379.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0375.stepData
  | 1=>Step0376.stepData
  | 2=>Step0377.stepData
  | 3=>Step0378.stepData
  | 4=>Step0379.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0375.stepData=true ∧
      (∀ i : Fin 7, Step0376.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0375.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0375.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0375.allStagesChecked,?_,Step0375.initialMarginCheck⟩
    intro i
    rw [Step0376.inputCoefficient,← Step0375.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0376.stepData=true ∧
      (∀ i : Fin 7, Step0377.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0376.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0376.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0376.allStagesChecked,?_,Step0376.initialMarginCheck⟩
    intro i
    rw [Step0377.inputCoefficient,← Step0376.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0377.stepData=true ∧
      (∀ i : Fin 7, Step0378.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0377.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0377.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0377.allStagesChecked,?_,Step0377.initialMarginCheck⟩
    intro i
    rw [Step0378.inputCoefficient,← Step0377.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0378.stepData=true ∧
      (∀ i : Fin 7, Step0379.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0378.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0378.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0378.allStagesChecked,?_,Step0378.initialMarginCheck⟩
    intro i
    rw [Step0379.inputCoefficient,← Step0378.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0379.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0379.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0379.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0379.allStagesChecked,?_,Step0379.initialMarginCheck⟩
    intro i
    change Step0379.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0379.stepData)[i.val]
    rw [← Step0379.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0375.stepData.coefficient 0 i=Step0375.inputData[i.val]
  exact Step0375.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Block0005
