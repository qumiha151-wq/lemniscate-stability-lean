import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0215
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0216
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0217
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0218
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0219

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0216.inputData=Step0215.endpointData := by decide +kernel

theorem glue1 : Step0217.inputData=Step0216.endpointData := by decide +kernel

theorem glue2 : Step0218.inputData=Step0217.endpointData := by decide +kernel

theorem glue3 : Step0219.inputData=Step0218.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0215.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0219.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0215.stepData
  | 1=>Step0216.stepData
  | 2=>Step0217.stepData
  | 3=>Step0218.stepData
  | 4=>Step0219.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0215.stepData=true ∧
      (∀ i : Fin 7, Step0216.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0215.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0215.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0215.allStagesChecked,?_,Step0215.initialMarginCheck⟩
    intro i
    rw [Step0216.inputCoefficient,← Step0215.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0216.stepData=true ∧
      (∀ i : Fin 7, Step0217.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0216.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0216.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0216.allStagesChecked,?_,Step0216.initialMarginCheck⟩
    intro i
    rw [Step0217.inputCoefficient,← Step0216.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0217.stepData=true ∧
      (∀ i : Fin 7, Step0218.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0217.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0217.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0217.allStagesChecked,?_,Step0217.initialMarginCheck⟩
    intro i
    rw [Step0218.inputCoefficient,← Step0217.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0218.stepData=true ∧
      (∀ i : Fin 7, Step0219.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0218.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0218.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0218.allStagesChecked,?_,Step0218.initialMarginCheck⟩
    intro i
    rw [Step0219.inputCoefficient,← Step0218.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0219.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0219.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0219.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0219.allStagesChecked,?_,Step0219.initialMarginCheck⟩
    intro i
    change Step0219.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0219.stepData)[i.val]
    rw [← Step0219.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0215.stepData.coefficient 0 i=Step0215.inputData[i.val]
  exact Step0215.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0003
