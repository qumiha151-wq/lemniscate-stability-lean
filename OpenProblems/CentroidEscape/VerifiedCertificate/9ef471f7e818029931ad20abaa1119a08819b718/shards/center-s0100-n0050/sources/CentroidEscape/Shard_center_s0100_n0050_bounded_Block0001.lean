import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0105
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0106
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0107
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0108
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0109

namespace CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0106.inputData=Step0105.endpointData := by decide +kernel

theorem glue1 : Step0107.inputData=Step0106.endpointData := by decide +kernel

theorem glue2 : Step0108.inputData=Step0107.endpointData := by decide +kernel

theorem glue3 : Step0109.inputData=Step0108.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0105.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0109.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0105.stepData
  | 1=>Step0106.stepData
  | 2=>Step0107.stepData
  | 3=>Step0108.stepData
  | 4=>Step0109.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0105.stepData=true ∧
      (∀ i : Fin 7, Step0106.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0105.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0105.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0105.allStagesChecked,?_,Step0105.initialMarginCheck⟩
    intro i
    rw [Step0106.inputCoefficient,← Step0105.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0106.stepData=true ∧
      (∀ i : Fin 7, Step0107.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0106.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0106.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0106.allStagesChecked,?_,Step0106.initialMarginCheck⟩
    intro i
    rw [Step0107.inputCoefficient,← Step0106.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0107.stepData=true ∧
      (∀ i : Fin 7, Step0108.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0107.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0107.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0107.allStagesChecked,?_,Step0107.initialMarginCheck⟩
    intro i
    rw [Step0108.inputCoefficient,← Step0107.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0108.stepData=true ∧
      (∀ i : Fin 7, Step0109.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0108.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0108.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0108.allStagesChecked,?_,Step0108.initialMarginCheck⟩
    intro i
    rw [Step0109.inputCoefficient,← Step0108.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0109.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0109.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0109.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0109.allStagesChecked,?_,Step0109.initialMarginCheck⟩
    intro i
    change Step0109.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0109.stepData)[i.val]
    rw [← Step0109.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0105.stepData.coefficient 0 i=Step0105.inputData[i.val]
  exact Step0105.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Block0001
