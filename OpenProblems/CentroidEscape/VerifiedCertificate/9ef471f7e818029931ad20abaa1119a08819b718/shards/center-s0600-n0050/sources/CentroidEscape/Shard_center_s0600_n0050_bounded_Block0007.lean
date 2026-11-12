import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0635
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0636
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0637
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0638
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0639

namespace CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0636.inputData=Step0635.endpointData := by decide +kernel

theorem glue1 : Step0637.inputData=Step0636.endpointData := by decide +kernel

theorem glue2 : Step0638.inputData=Step0637.endpointData := by decide +kernel

theorem glue3 : Step0639.inputData=Step0638.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0635.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0639.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0635.stepData
  | 1=>Step0636.stepData
  | 2=>Step0637.stepData
  | 3=>Step0638.stepData
  | 4=>Step0639.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0635.stepData=true ∧
      (∀ i : Fin 7, Step0636.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0635.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0635.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0635.allStagesChecked,?_,Step0635.initialMarginCheck⟩
    intro i
    rw [Step0636.inputCoefficient,← Step0635.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0636.stepData=true ∧
      (∀ i : Fin 7, Step0637.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0636.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0636.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0636.allStagesChecked,?_,Step0636.initialMarginCheck⟩
    intro i
    rw [Step0637.inputCoefficient,← Step0636.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0637.stepData=true ∧
      (∀ i : Fin 7, Step0638.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0637.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0637.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0637.allStagesChecked,?_,Step0637.initialMarginCheck⟩
    intro i
    rw [Step0638.inputCoefficient,← Step0637.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0638.stepData=true ∧
      (∀ i : Fin 7, Step0639.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0638.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0638.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0638.allStagesChecked,?_,Step0638.initialMarginCheck⟩
    intro i
    rw [Step0639.inputCoefficient,← Step0638.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0639.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0639.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0639.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0639.allStagesChecked,?_,Step0639.initialMarginCheck⟩
    intro i
    change Step0639.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0639.stepData)[i.val]
    rw [← Step0639.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0635.stepData.coefficient 0 i=Step0635.inputData[i.val]
  exact Step0635.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Block0007
