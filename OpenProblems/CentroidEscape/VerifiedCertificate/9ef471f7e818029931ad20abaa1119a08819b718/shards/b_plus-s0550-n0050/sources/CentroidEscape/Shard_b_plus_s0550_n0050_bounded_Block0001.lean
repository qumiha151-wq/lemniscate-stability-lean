import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0555
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0556
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0557
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0558
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0559

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0556.inputData=Step0555.endpointData := by decide +kernel

theorem glue1 : Step0557.inputData=Step0556.endpointData := by decide +kernel

theorem glue2 : Step0558.inputData=Step0557.endpointData := by decide +kernel

theorem glue3 : Step0559.inputData=Step0558.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0555.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0559.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0555.stepData
  | 1=>Step0556.stepData
  | 2=>Step0557.stepData
  | 3=>Step0558.stepData
  | 4=>Step0559.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0555.stepData=true ∧
      (∀ i : Fin 7, Step0556.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0555.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0555.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0555.allStagesChecked,?_,Step0555.initialMarginCheck⟩
    intro i
    rw [Step0556.inputCoefficient,← Step0555.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0556.stepData=true ∧
      (∀ i : Fin 7, Step0557.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0556.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0556.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0556.allStagesChecked,?_,Step0556.initialMarginCheck⟩
    intro i
    rw [Step0557.inputCoefficient,← Step0556.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0557.stepData=true ∧
      (∀ i : Fin 7, Step0558.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0557.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0557.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0557.allStagesChecked,?_,Step0557.initialMarginCheck⟩
    intro i
    rw [Step0558.inputCoefficient,← Step0557.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0558.stepData=true ∧
      (∀ i : Fin 7, Step0559.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0558.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0558.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0558.allStagesChecked,?_,Step0558.initialMarginCheck⟩
    intro i
    rw [Step0559.inputCoefficient,← Step0558.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0559.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0559.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0559.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0559.allStagesChecked,?_,Step0559.initialMarginCheck⟩
    intro i
    change Step0559.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0559.stepData)[i.val]
    rw [← Step0559.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0555.stepData.coefficient 0 i=Step0555.inputData[i.val]
  exact Step0555.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Block0001
