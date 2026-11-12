import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0205
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0206
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0207
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0208
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0209

namespace CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0206.inputData=Step0205.endpointData := by decide +kernel

theorem glue1 : Step0207.inputData=Step0206.endpointData := by decide +kernel

theorem glue2 : Step0208.inputData=Step0207.endpointData := by decide +kernel

theorem glue3 : Step0209.inputData=Step0208.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0205.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0209.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0205.stepData
  | 1=>Step0206.stepData
  | 2=>Step0207.stepData
  | 3=>Step0208.stepData
  | 4=>Step0209.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0205.stepData=true ∧
      (∀ i : Fin 7, Step0206.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0205.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0205.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0205.allStagesChecked,?_,Step0205.initialMarginCheck⟩
    intro i
    rw [Step0206.inputCoefficient,← Step0205.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0206.stepData=true ∧
      (∀ i : Fin 7, Step0207.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0206.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0206.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0206.allStagesChecked,?_,Step0206.initialMarginCheck⟩
    intro i
    rw [Step0207.inputCoefficient,← Step0206.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0207.stepData=true ∧
      (∀ i : Fin 7, Step0208.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0207.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0207.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0207.allStagesChecked,?_,Step0207.initialMarginCheck⟩
    intro i
    rw [Step0208.inputCoefficient,← Step0207.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0208.stepData=true ∧
      (∀ i : Fin 7, Step0209.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0208.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0208.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0208.allStagesChecked,?_,Step0208.initialMarginCheck⟩
    intro i
    rw [Step0209.inputCoefficient,← Step0208.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0209.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0209.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0209.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0209.allStagesChecked,?_,Step0209.initialMarginCheck⟩
    intro i
    change Step0209.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0209.stepData)[i.val]
    rw [← Step0209.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0205.stepData.coefficient 0 i=Step0205.inputData[i.val]
  exact Step0205.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Block0001
