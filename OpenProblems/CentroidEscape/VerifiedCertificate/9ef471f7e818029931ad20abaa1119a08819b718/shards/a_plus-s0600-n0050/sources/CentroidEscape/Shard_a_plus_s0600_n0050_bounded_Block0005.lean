import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0625
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0626
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0627
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0628
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Step0629

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0626.inputData=Step0625.endpointData := by decide +kernel

theorem glue1 : Step0627.inputData=Step0626.endpointData := by decide +kernel

theorem glue2 : Step0628.inputData=Step0627.endpointData := by decide +kernel

theorem glue3 : Step0629.inputData=Step0628.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0625.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0629.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0625.stepData
  | 1=>Step0626.stepData
  | 2=>Step0627.stepData
  | 3=>Step0628.stepData
  | 4=>Step0629.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0625.stepData=true ∧
      (∀ i : Fin 7, Step0626.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0625.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0625.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0625.allStagesChecked,?_,Step0625.initialMarginCheck⟩
    intro i
    rw [Step0626.inputCoefficient,← Step0625.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0626.stepData=true ∧
      (∀ i : Fin 7, Step0627.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0626.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0626.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0626.allStagesChecked,?_,Step0626.initialMarginCheck⟩
    intro i
    rw [Step0627.inputCoefficient,← Step0626.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0627.stepData=true ∧
      (∀ i : Fin 7, Step0628.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0627.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0627.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0627.allStagesChecked,?_,Step0627.initialMarginCheck⟩
    intro i
    rw [Step0628.inputCoefficient,← Step0627.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0628.stepData=true ∧
      (∀ i : Fin 7, Step0629.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0628.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0628.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0628.allStagesChecked,?_,Step0628.initialMarginCheck⟩
    intro i
    rw [Step0629.inputCoefficient,← Step0628.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0629.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0629.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0629.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0629.allStagesChecked,?_,Step0629.initialMarginCheck⟩
    intro i
    change Step0629.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0629.stepData)[i.val]
    rw [← Step0629.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0625.stepData.coefficient 0 i=Step0625.inputData[i.val]
  exact Step0625.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Block0005
