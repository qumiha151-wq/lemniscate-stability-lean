import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0250_n0050_bounded_Step0275
import CentroidEscape.Shard_b_plus_s0250_n0050_bounded_Step0276
import CentroidEscape.Shard_b_plus_s0250_n0050_bounded_Step0277
import CentroidEscape.Shard_b_plus_s0250_n0050_bounded_Step0278
import CentroidEscape.Shard_b_plus_s0250_n0050_bounded_Step0279

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0276.inputData=Step0275.endpointData := by decide +kernel

theorem glue1 : Step0277.inputData=Step0276.endpointData := by decide +kernel

theorem glue2 : Step0278.inputData=Step0277.endpointData := by decide +kernel

theorem glue3 : Step0279.inputData=Step0278.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0275.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0279.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0275.stepData
  | 1=>Step0276.stepData
  | 2=>Step0277.stepData
  | 3=>Step0278.stepData
  | 4=>Step0279.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0275.stepData=true ∧
      (∀ i : Fin 7, Step0276.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0275.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0275.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0275.allStagesChecked,?_,Step0275.initialMarginCheck⟩
    intro i
    rw [Step0276.inputCoefficient,← Step0275.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0276.stepData=true ∧
      (∀ i : Fin 7, Step0277.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0276.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0276.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0276.allStagesChecked,?_,Step0276.initialMarginCheck⟩
    intro i
    rw [Step0277.inputCoefficient,← Step0276.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0277.stepData=true ∧
      (∀ i : Fin 7, Step0278.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0277.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0277.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0277.allStagesChecked,?_,Step0277.initialMarginCheck⟩
    intro i
    rw [Step0278.inputCoefficient,← Step0277.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0278.stepData=true ∧
      (∀ i : Fin 7, Step0279.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0278.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0278.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0278.allStagesChecked,?_,Step0278.initialMarginCheck⟩
    intro i
    rw [Step0279.inputCoefficient,← Step0278.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0279.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0279.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0279.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0279.allStagesChecked,?_,Step0279.initialMarginCheck⟩
    intro i
    change Step0279.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0279.stepData)[i.val]
    rw [← Step0279.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0275.stepData.coefficient 0 i=Step0275.inputData[i.val]
  exact Step0275.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Block0005
