import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0240
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0241
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0242
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0243
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0244

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0241.inputData=Step0240.endpointData := by decide +kernel

theorem glue1 : Step0242.inputData=Step0241.endpointData := by decide +kernel

theorem glue2 : Step0243.inputData=Step0242.endpointData := by decide +kernel

theorem glue3 : Step0244.inputData=Step0243.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0240.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0244.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0240.stepData
  | 1=>Step0241.stepData
  | 2=>Step0242.stepData
  | 3=>Step0243.stepData
  | 4=>Step0244.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0240.stepData=true ∧
      (∀ i : Fin 7, Step0241.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0240.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0240.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0240.allStagesChecked,?_,Step0240.initialMarginCheck⟩
    intro i
    rw [Step0241.inputCoefficient,← Step0240.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0241.stepData=true ∧
      (∀ i : Fin 7, Step0242.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0241.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0241.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0241.allStagesChecked,?_,Step0241.initialMarginCheck⟩
    intro i
    rw [Step0242.inputCoefficient,← Step0241.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0242.stepData=true ∧
      (∀ i : Fin 7, Step0243.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0242.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0242.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0242.allStagesChecked,?_,Step0242.initialMarginCheck⟩
    intro i
    rw [Step0243.inputCoefficient,← Step0242.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0243.stepData=true ∧
      (∀ i : Fin 7, Step0244.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0243.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0243.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0243.allStagesChecked,?_,Step0243.initialMarginCheck⟩
    intro i
    rw [Step0244.inputCoefficient,← Step0243.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0244.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0244.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0244.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0244.allStagesChecked,?_,Step0244.initialMarginCheck⟩
    intro i
    change Step0244.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0244.stepData)[i.val]
    rw [← Step0244.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0240.stepData.coefficient 0 i=Step0240.inputData[i.val]
  exact Step0240.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0008
