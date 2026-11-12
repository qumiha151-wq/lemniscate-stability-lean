import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0200_n0050_bounded_Step0200
import CentroidEscape.Shard_b_plus_s0200_n0050_bounded_Step0201
import CentroidEscape.Shard_b_plus_s0200_n0050_bounded_Step0202
import CentroidEscape.Shard_b_plus_s0200_n0050_bounded_Step0203
import CentroidEscape.Shard_b_plus_s0200_n0050_bounded_Step0204

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0201.inputData=Step0200.endpointData := by decide +kernel

theorem glue1 : Step0202.inputData=Step0201.endpointData := by decide +kernel

theorem glue2 : Step0203.inputData=Step0202.endpointData := by decide +kernel

theorem glue3 : Step0204.inputData=Step0203.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0200.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0204.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0200.stepData
  | 1=>Step0201.stepData
  | 2=>Step0202.stepData
  | 3=>Step0203.stepData
  | 4=>Step0204.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0200.stepData=true ∧
      (∀ i : Fin 7, Step0201.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0200.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0200.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0200.allStagesChecked,?_,Step0200.initialMarginCheck⟩
    intro i
    rw [Step0201.inputCoefficient,← Step0200.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0201.stepData=true ∧
      (∀ i : Fin 7, Step0202.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0201.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0201.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0201.allStagesChecked,?_,Step0201.initialMarginCheck⟩
    intro i
    rw [Step0202.inputCoefficient,← Step0201.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0202.stepData=true ∧
      (∀ i : Fin 7, Step0203.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0202.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0202.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0202.allStagesChecked,?_,Step0202.initialMarginCheck⟩
    intro i
    rw [Step0203.inputCoefficient,← Step0202.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0203.stepData=true ∧
      (∀ i : Fin 7, Step0204.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0203.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0203.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0203.allStagesChecked,?_,Step0203.initialMarginCheck⟩
    intro i
    rw [Step0204.inputCoefficient,← Step0203.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0204.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0204.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0204.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0204.allStagesChecked,?_,Step0204.initialMarginCheck⟩
    intro i
    change Step0204.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0204.stepData)[i.val]
    rw [← Step0204.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0200.stepData.coefficient 0 i=Step0200.inputData[i.val]
  exact Step0200.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Block0000
