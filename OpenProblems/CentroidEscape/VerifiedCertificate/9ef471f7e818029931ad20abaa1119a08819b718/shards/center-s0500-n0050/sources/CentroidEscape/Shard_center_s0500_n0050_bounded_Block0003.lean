import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0515
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0516
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0517
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0518
import CentroidEscape.Shard_center_s0500_n0050_bounded_Step0519

namespace CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0516.inputData=Step0515.endpointData := by decide +kernel

theorem glue1 : Step0517.inputData=Step0516.endpointData := by decide +kernel

theorem glue2 : Step0518.inputData=Step0517.endpointData := by decide +kernel

theorem glue3 : Step0519.inputData=Step0518.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0515.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0519.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0515.stepData
  | 1=>Step0516.stepData
  | 2=>Step0517.stepData
  | 3=>Step0518.stepData
  | 4=>Step0519.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0515.stepData=true ∧
      (∀ i : Fin 7, Step0516.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0515.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0515.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0515.allStagesChecked,?_,Step0515.initialMarginCheck⟩
    intro i
    rw [Step0516.inputCoefficient,← Step0515.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0516.stepData=true ∧
      (∀ i : Fin 7, Step0517.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0516.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0516.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0516.allStagesChecked,?_,Step0516.initialMarginCheck⟩
    intro i
    rw [Step0517.inputCoefficient,← Step0516.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0517.stepData=true ∧
      (∀ i : Fin 7, Step0518.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0517.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0517.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0517.allStagesChecked,?_,Step0517.initialMarginCheck⟩
    intro i
    rw [Step0518.inputCoefficient,← Step0517.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0518.stepData=true ∧
      (∀ i : Fin 7, Step0519.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0518.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0518.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0518.allStagesChecked,?_,Step0518.initialMarginCheck⟩
    intro i
    rw [Step0519.inputCoefficient,← Step0518.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0519.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0519.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0519.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0519.allStagesChecked,?_,Step0519.initialMarginCheck⟩
    intro i
    change Step0519.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0519.stepData)[i.val]
    rw [← Step0519.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0515.stepData.coefficient 0 i=Step0515.inputData[i.val]
  exact Step0515.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Block0003
