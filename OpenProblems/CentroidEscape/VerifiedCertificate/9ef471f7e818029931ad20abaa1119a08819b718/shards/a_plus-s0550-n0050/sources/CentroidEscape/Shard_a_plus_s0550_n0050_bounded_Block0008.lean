import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0590
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0591
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0592
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0593
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Step0594

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0591.inputData=Step0590.endpointData := by decide +kernel

theorem glue1 : Step0592.inputData=Step0591.endpointData := by decide +kernel

theorem glue2 : Step0593.inputData=Step0592.endpointData := by decide +kernel

theorem glue3 : Step0594.inputData=Step0593.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0590.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0594.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0590.stepData
  | 1=>Step0591.stepData
  | 2=>Step0592.stepData
  | 3=>Step0593.stepData
  | 4=>Step0594.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0590.stepData=true ∧
      (∀ i : Fin 7, Step0591.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0590.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0590.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0590.allStagesChecked,?_,Step0590.initialMarginCheck⟩
    intro i
    rw [Step0591.inputCoefficient,← Step0590.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0591.stepData=true ∧
      (∀ i : Fin 7, Step0592.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0591.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0591.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0591.allStagesChecked,?_,Step0591.initialMarginCheck⟩
    intro i
    rw [Step0592.inputCoefficient,← Step0591.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0592.stepData=true ∧
      (∀ i : Fin 7, Step0593.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0592.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0592.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0592.allStagesChecked,?_,Step0592.initialMarginCheck⟩
    intro i
    rw [Step0593.inputCoefficient,← Step0592.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0593.stepData=true ∧
      (∀ i : Fin 7, Step0594.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0593.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0593.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0593.allStagesChecked,?_,Step0593.initialMarginCheck⟩
    intro i
    rw [Step0594.inputCoefficient,← Step0593.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0594.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0594.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0594.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0594.allStagesChecked,?_,Step0594.initialMarginCheck⟩
    intro i
    change Step0594.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0594.stepData)[i.val]
    rw [← Step0594.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0590.stepData.coefficient 0 i=Step0590.inputData[i.val]
  exact Step0590.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Block0008
