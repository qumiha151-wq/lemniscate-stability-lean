import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0185
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0186
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0187
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0188
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0189

namespace CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0186.inputData=Step0185.endpointData := by decide +kernel

theorem glue1 : Step0187.inputData=Step0186.endpointData := by decide +kernel

theorem glue2 : Step0188.inputData=Step0187.endpointData := by decide +kernel

theorem glue3 : Step0189.inputData=Step0188.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0185.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0189.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0185.stepData
  | 1=>Step0186.stepData
  | 2=>Step0187.stepData
  | 3=>Step0188.stepData
  | 4=>Step0189.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0185.stepData=true ∧
      (∀ i : Fin 7, Step0186.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0185.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0185.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0185.allStagesChecked,?_,Step0185.initialMarginCheck⟩
    intro i
    rw [Step0186.inputCoefficient,← Step0185.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0186.stepData=true ∧
      (∀ i : Fin 7, Step0187.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0186.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0186.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0186.allStagesChecked,?_,Step0186.initialMarginCheck⟩
    intro i
    rw [Step0187.inputCoefficient,← Step0186.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0187.stepData=true ∧
      (∀ i : Fin 7, Step0188.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0187.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0187.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0187.allStagesChecked,?_,Step0187.initialMarginCheck⟩
    intro i
    rw [Step0188.inputCoefficient,← Step0187.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0188.stepData=true ∧
      (∀ i : Fin 7, Step0189.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0188.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0188.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0188.allStagesChecked,?_,Step0188.initialMarginCheck⟩
    intro i
    rw [Step0189.inputCoefficient,← Step0188.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0189.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0189.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0189.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0189.allStagesChecked,?_,Step0189.initialMarginCheck⟩
    intro i
    change Step0189.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0189.stepData)[i.val]
    rw [← Step0189.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0185.stepData.coefficient 0 i=Step0185.inputData[i.val]
  exact Step0185.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0007
