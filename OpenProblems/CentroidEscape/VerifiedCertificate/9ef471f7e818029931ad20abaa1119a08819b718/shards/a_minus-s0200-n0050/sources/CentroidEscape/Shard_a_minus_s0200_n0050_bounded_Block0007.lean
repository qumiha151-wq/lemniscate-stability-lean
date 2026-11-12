import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0235
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0236
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0237
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0238
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0239

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0236.inputData=Step0235.endpointData := by decide +kernel

theorem glue1 : Step0237.inputData=Step0236.endpointData := by decide +kernel

theorem glue2 : Step0238.inputData=Step0237.endpointData := by decide +kernel

theorem glue3 : Step0239.inputData=Step0238.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0235.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0239.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0235.stepData
  | 1=>Step0236.stepData
  | 2=>Step0237.stepData
  | 3=>Step0238.stepData
  | 4=>Step0239.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0235.stepData=true ∧
      (∀ i : Fin 7, Step0236.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0235.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0235.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0235.allStagesChecked,?_,Step0235.initialMarginCheck⟩
    intro i
    rw [Step0236.inputCoefficient,← Step0235.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0236.stepData=true ∧
      (∀ i : Fin 7, Step0237.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0236.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0236.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0236.allStagesChecked,?_,Step0236.initialMarginCheck⟩
    intro i
    rw [Step0237.inputCoefficient,← Step0236.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0237.stepData=true ∧
      (∀ i : Fin 7, Step0238.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0237.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0237.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0237.allStagesChecked,?_,Step0237.initialMarginCheck⟩
    intro i
    rw [Step0238.inputCoefficient,← Step0237.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0238.stepData=true ∧
      (∀ i : Fin 7, Step0239.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0238.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0238.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0238.allStagesChecked,?_,Step0238.initialMarginCheck⟩
    intro i
    rw [Step0239.inputCoefficient,← Step0238.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0239.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0239.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0239.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0239.allStagesChecked,?_,Step0239.initialMarginCheck⟩
    intro i
    change Step0239.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0239.stepData)[i.val]
    rw [← Step0239.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0235.stepData.coefficient 0 i=Step0235.inputData[i.val]
  exact Step0235.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Block0007
