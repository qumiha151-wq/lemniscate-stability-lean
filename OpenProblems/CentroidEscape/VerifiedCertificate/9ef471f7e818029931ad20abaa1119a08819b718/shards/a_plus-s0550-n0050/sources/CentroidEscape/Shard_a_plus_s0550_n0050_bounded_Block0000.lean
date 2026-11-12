import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0550
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0551
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0552
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0553
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0554

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0551.inputData=Step0550.endpointData := by decide +kernel

theorem glue1 : Step0552.inputData=Step0551.endpointData := by decide +kernel

theorem glue2 : Step0553.inputData=Step0552.endpointData := by decide +kernel

theorem glue3 : Step0554.inputData=Step0553.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0550.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0554.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0550.stepData
  | 1=>Step0551.stepData
  | 2=>Step0552.stepData
  | 3=>Step0553.stepData
  | 4=>Step0554.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0550.stepData=true ∧
      (∀ i : Fin 7, Step0551.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0550.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0550.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0550.allStagesChecked,?_,Step0550.initialMarginCheck⟩
    intro i
    rw [Step0551.inputCoefficient,← Step0550.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0551.stepData=true ∧
      (∀ i : Fin 7, Step0552.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0551.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0551.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0551.allStagesChecked,?_,Step0551.initialMarginCheck⟩
    intro i
    rw [Step0552.inputCoefficient,← Step0551.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0552.stepData=true ∧
      (∀ i : Fin 7, Step0553.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0552.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0552.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0552.allStagesChecked,?_,Step0552.initialMarginCheck⟩
    intro i
    rw [Step0553.inputCoefficient,← Step0552.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0553.stepData=true ∧
      (∀ i : Fin 7, Step0554.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0553.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0553.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0553.allStagesChecked,?_,Step0553.initialMarginCheck⟩
    intro i
    rw [Step0554.inputCoefficient,← Step0553.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0554.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0554.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0554.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0554.allStagesChecked,?_,Step0554.initialMarginCheck⟩
    intro i
    change Step0554.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0554.stepData)[i.val]
    rw [← Step0554.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0550.stepData.coefficient 0 i=Step0550.inputData[i.val]
  exact Step0550.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Block0000
