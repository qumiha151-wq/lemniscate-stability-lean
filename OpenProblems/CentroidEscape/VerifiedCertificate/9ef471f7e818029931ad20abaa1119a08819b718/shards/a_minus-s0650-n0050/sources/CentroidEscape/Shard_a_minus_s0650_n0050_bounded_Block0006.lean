import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0680
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0681
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0682
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0683
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0684

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0681.inputData=Step0680.endpointData := by decide +kernel

theorem glue1 : Step0682.inputData=Step0681.endpointData := by decide +kernel

theorem glue2 : Step0683.inputData=Step0682.endpointData := by decide +kernel

theorem glue3 : Step0684.inputData=Step0683.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0680.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0684.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0680.stepData
  | 1=>Step0681.stepData
  | 2=>Step0682.stepData
  | 3=>Step0683.stepData
  | 4=>Step0684.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0680.stepData=true ∧
      (∀ i : Fin 7, Step0681.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0680.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0680.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0680.allStagesChecked,?_,Step0680.initialMarginCheck⟩
    intro i
    rw [Step0681.inputCoefficient,← Step0680.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0681.stepData=true ∧
      (∀ i : Fin 7, Step0682.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0681.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0681.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0681.allStagesChecked,?_,Step0681.initialMarginCheck⟩
    intro i
    rw [Step0682.inputCoefficient,← Step0681.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0682.stepData=true ∧
      (∀ i : Fin 7, Step0683.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0682.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0682.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0682.allStagesChecked,?_,Step0682.initialMarginCheck⟩
    intro i
    rw [Step0683.inputCoefficient,← Step0682.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0683.stepData=true ∧
      (∀ i : Fin 7, Step0684.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0683.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0683.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0683.allStagesChecked,?_,Step0683.initialMarginCheck⟩
    intro i
    rw [Step0684.inputCoefficient,← Step0683.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0684.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0684.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0684.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0684.allStagesChecked,?_,Step0684.initialMarginCheck⟩
    intro i
    change Step0684.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0684.stepData)[i.val]
    rw [← Step0684.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0680.stepData.coefficient 0 i=Step0680.inputData[i.val]
  exact Step0680.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Block0006
