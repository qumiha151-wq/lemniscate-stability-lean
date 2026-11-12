import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0620
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0621
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0622
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0623
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0624

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0621.inputData=Step0620.endpointData := by decide +kernel

theorem glue1 : Step0622.inputData=Step0621.endpointData := by decide +kernel

theorem glue2 : Step0623.inputData=Step0622.endpointData := by decide +kernel

theorem glue3 : Step0624.inputData=Step0623.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0620.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0624.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0620.stepData
  | 1=>Step0621.stepData
  | 2=>Step0622.stepData
  | 3=>Step0623.stepData
  | 4=>Step0624.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0620.stepData=true ∧
      (∀ i : Fin 7, Step0621.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0620.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0620.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0620.allStagesChecked,?_,Step0620.initialMarginCheck⟩
    intro i
    rw [Step0621.inputCoefficient,← Step0620.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0621.stepData=true ∧
      (∀ i : Fin 7, Step0622.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0621.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0621.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0621.allStagesChecked,?_,Step0621.initialMarginCheck⟩
    intro i
    rw [Step0622.inputCoefficient,← Step0621.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0622.stepData=true ∧
      (∀ i : Fin 7, Step0623.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0622.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0622.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0622.allStagesChecked,?_,Step0622.initialMarginCheck⟩
    intro i
    rw [Step0623.inputCoefficient,← Step0622.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0623.stepData=true ∧
      (∀ i : Fin 7, Step0624.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0623.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0623.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0623.allStagesChecked,?_,Step0623.initialMarginCheck⟩
    intro i
    rw [Step0624.inputCoefficient,← Step0623.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0624.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0624.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0624.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0624.allStagesChecked,?_,Step0624.initialMarginCheck⟩
    intro i
    change Step0624.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0624.stepData)[i.val]
    rw [← Step0624.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0620.stepData.coefficient 0 i=Step0620.inputData[i.val]
  exact Step0620.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0004
