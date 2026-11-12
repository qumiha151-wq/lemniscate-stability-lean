import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0695
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0696
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0697
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0698
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0699

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0696.inputData=Step0695.endpointData := by decide +kernel

theorem glue1 : Step0697.inputData=Step0696.endpointData := by decide +kernel

theorem glue2 : Step0698.inputData=Step0697.endpointData := by decide +kernel

theorem glue3 : Step0699.inputData=Step0698.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0695.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0699.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0695.stepData
  | 1=>Step0696.stepData
  | 2=>Step0697.stepData
  | 3=>Step0698.stepData
  | 4=>Step0699.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0695.stepData=true ∧
      (∀ i : Fin 7, Step0696.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0695.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0695.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0695.allStagesChecked,?_,Step0695.initialMarginCheck⟩
    intro i
    rw [Step0696.inputCoefficient,← Step0695.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0696.stepData=true ∧
      (∀ i : Fin 7, Step0697.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0696.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0696.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0696.allStagesChecked,?_,Step0696.initialMarginCheck⟩
    intro i
    rw [Step0697.inputCoefficient,← Step0696.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0697.stepData=true ∧
      (∀ i : Fin 7, Step0698.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0697.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0697.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0697.allStagesChecked,?_,Step0697.initialMarginCheck⟩
    intro i
    rw [Step0698.inputCoefficient,← Step0697.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0698.stepData=true ∧
      (∀ i : Fin 7, Step0699.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0698.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0698.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0698.allStagesChecked,?_,Step0698.initialMarginCheck⟩
    intro i
    rw [Step0699.inputCoefficient,← Step0698.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0699.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0699.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0699.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0699.allStagesChecked,?_,Step0699.initialMarginCheck⟩
    intro i
    change Step0699.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0699.stepData)[i.val]
    rw [← Step0699.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0695.stepData.coefficient 0 i=Step0695.inputData[i.val]
  exact Step0695.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Block0009
