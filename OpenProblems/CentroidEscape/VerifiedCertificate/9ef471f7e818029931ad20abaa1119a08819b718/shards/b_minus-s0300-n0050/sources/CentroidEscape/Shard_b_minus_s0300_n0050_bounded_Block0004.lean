import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0320
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0321
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0322
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0323
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0324

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0321.inputData=Step0320.endpointData := by decide +kernel

theorem glue1 : Step0322.inputData=Step0321.endpointData := by decide +kernel

theorem glue2 : Step0323.inputData=Step0322.endpointData := by decide +kernel

theorem glue3 : Step0324.inputData=Step0323.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0320.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0324.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0320.stepData
  | 1=>Step0321.stepData
  | 2=>Step0322.stepData
  | 3=>Step0323.stepData
  | 4=>Step0324.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0320.stepData=true ∧
      (∀ i : Fin 7, Step0321.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0320.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0320.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0320.allStagesChecked,?_,Step0320.initialMarginCheck⟩
    intro i
    rw [Step0321.inputCoefficient,← Step0320.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0321.stepData=true ∧
      (∀ i : Fin 7, Step0322.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0321.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0321.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0321.allStagesChecked,?_,Step0321.initialMarginCheck⟩
    intro i
    rw [Step0322.inputCoefficient,← Step0321.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0322.stepData=true ∧
      (∀ i : Fin 7, Step0323.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0322.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0322.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0322.allStagesChecked,?_,Step0322.initialMarginCheck⟩
    intro i
    rw [Step0323.inputCoefficient,← Step0322.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0323.stepData=true ∧
      (∀ i : Fin 7, Step0324.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0323.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0323.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0323.allStagesChecked,?_,Step0323.initialMarginCheck⟩
    intro i
    rw [Step0324.inputCoefficient,← Step0323.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0324.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0324.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0324.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0324.allStagesChecked,?_,Step0324.initialMarginCheck⟩
    intro i
    change Step0324.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0324.stepData)[i.val]
    rw [← Step0324.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0320.stepData.coefficient 0 i=Step0320.inputData[i.val]
  exact Step0320.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Block0004
