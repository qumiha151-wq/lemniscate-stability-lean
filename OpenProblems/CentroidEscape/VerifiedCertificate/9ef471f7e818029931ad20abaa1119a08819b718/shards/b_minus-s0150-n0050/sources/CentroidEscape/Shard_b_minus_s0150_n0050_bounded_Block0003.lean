import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0165
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0166
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0167
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0168
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0169

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0166.inputData=Step0165.endpointData := by decide +kernel

theorem glue1 : Step0167.inputData=Step0166.endpointData := by decide +kernel

theorem glue2 : Step0168.inputData=Step0167.endpointData := by decide +kernel

theorem glue3 : Step0169.inputData=Step0168.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0165.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0169.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0165.stepData
  | 1=>Step0166.stepData
  | 2=>Step0167.stepData
  | 3=>Step0168.stepData
  | 4=>Step0169.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0165.stepData=true ∧
      (∀ i : Fin 7, Step0166.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0165.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0165.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0165.allStagesChecked,?_,Step0165.initialMarginCheck⟩
    intro i
    rw [Step0166.inputCoefficient,← Step0165.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0166.stepData=true ∧
      (∀ i : Fin 7, Step0167.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0166.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0166.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0166.allStagesChecked,?_,Step0166.initialMarginCheck⟩
    intro i
    rw [Step0167.inputCoefficient,← Step0166.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0167.stepData=true ∧
      (∀ i : Fin 7, Step0168.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0167.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0167.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0167.allStagesChecked,?_,Step0167.initialMarginCheck⟩
    intro i
    rw [Step0168.inputCoefficient,← Step0167.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0168.stepData=true ∧
      (∀ i : Fin 7, Step0169.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0168.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0168.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0168.allStagesChecked,?_,Step0168.initialMarginCheck⟩
    intro i
    rw [Step0169.inputCoefficient,← Step0168.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0169.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0169.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0169.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0169.allStagesChecked,?_,Step0169.initialMarginCheck⟩
    intro i
    change Step0169.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0169.stepData)[i.val]
    rw [← Step0169.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0165.stepData.coefficient 0 i=Step0165.inputData[i.val]
  exact Step0165.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Block0003
