import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0150_n0050_bounded_Step0160
import CentroidEscape.Shard_b_plus_s0150_n0050_bounded_Step0161
import CentroidEscape.Shard_b_plus_s0150_n0050_bounded_Step0162
import CentroidEscape.Shard_b_plus_s0150_n0050_bounded_Step0163
import CentroidEscape.Shard_b_plus_s0150_n0050_bounded_Step0164

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0161.inputData=Step0160.endpointData := by decide +kernel

theorem glue1 : Step0162.inputData=Step0161.endpointData := by decide +kernel

theorem glue2 : Step0163.inputData=Step0162.endpointData := by decide +kernel

theorem glue3 : Step0164.inputData=Step0163.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0160.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0164.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0160.stepData
  | 1=>Step0161.stepData
  | 2=>Step0162.stepData
  | 3=>Step0163.stepData
  | 4=>Step0164.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0160.stepData=true ∧
      (∀ i : Fin 7, Step0161.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0160.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0160.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0160.allStagesChecked,?_,Step0160.initialMarginCheck⟩
    intro i
    rw [Step0161.inputCoefficient,← Step0160.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0161.stepData=true ∧
      (∀ i : Fin 7, Step0162.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0161.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0161.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0161.allStagesChecked,?_,Step0161.initialMarginCheck⟩
    intro i
    rw [Step0162.inputCoefficient,← Step0161.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0162.stepData=true ∧
      (∀ i : Fin 7, Step0163.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0162.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0162.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0162.allStagesChecked,?_,Step0162.initialMarginCheck⟩
    intro i
    rw [Step0163.inputCoefficient,← Step0162.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0163.stepData=true ∧
      (∀ i : Fin 7, Step0164.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0163.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0163.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0163.allStagesChecked,?_,Step0163.initialMarginCheck⟩
    intro i
    rw [Step0164.inputCoefficient,← Step0163.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0164.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0164.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0164.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0164.allStagesChecked,?_,Step0164.initialMarginCheck⟩
    intro i
    change Step0164.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0164.stepData)[i.val]
    rw [← Step0164.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0160.stepData.coefficient 0 i=Step0160.inputData[i.val]
  exact Step0160.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Block0002
