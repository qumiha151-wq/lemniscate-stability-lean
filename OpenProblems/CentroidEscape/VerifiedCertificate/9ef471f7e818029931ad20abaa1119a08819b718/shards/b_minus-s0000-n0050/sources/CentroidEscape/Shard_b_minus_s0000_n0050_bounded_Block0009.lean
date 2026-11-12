import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0045
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0046
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0047
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0048
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0049

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0000_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0046.inputData=Step0045.endpointData := by decide +kernel

theorem glue1 : Step0047.inputData=Step0046.endpointData := by decide +kernel

theorem glue2 : Step0048.inputData=Step0047.endpointData := by decide +kernel

theorem glue3 : Step0049.inputData=Step0048.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0045.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0049.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0045.stepData
  | 1=>Step0046.stepData
  | 2=>Step0047.stepData
  | 3=>Step0048.stepData
  | 4=>Step0049.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0045.stepData=true ∧
      (∀ i : Fin 7, Step0046.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0045.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0045.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0045.allStagesChecked,?_,Step0045.initialMarginCheck⟩
    intro i
    rw [Step0046.inputCoefficient,← Step0045.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0046.stepData=true ∧
      (∀ i : Fin 7, Step0047.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0046.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0046.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0046.allStagesChecked,?_,Step0046.initialMarginCheck⟩
    intro i
    rw [Step0047.inputCoefficient,← Step0046.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0047.stepData=true ∧
      (∀ i : Fin 7, Step0048.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0047.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0047.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0047.allStagesChecked,?_,Step0047.initialMarginCheck⟩
    intro i
    rw [Step0048.inputCoefficient,← Step0047.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0048.stepData=true ∧
      (∀ i : Fin 7, Step0049.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0048.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0048.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0048.allStagesChecked,?_,Step0048.initialMarginCheck⟩
    intro i
    rw [Step0049.inputCoefficient,← Step0048.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0049.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0049.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0049.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0049.allStagesChecked,?_,Step0049.initialMarginCheck⟩
    intro i
    change Step0049.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0049.stepData)[i.val]
    rw [← Step0049.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0045.stepData.coefficient 0 i=Step0045.inputData[i.val]
  exact Step0045.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0000_n0050_bounded.Block0009
