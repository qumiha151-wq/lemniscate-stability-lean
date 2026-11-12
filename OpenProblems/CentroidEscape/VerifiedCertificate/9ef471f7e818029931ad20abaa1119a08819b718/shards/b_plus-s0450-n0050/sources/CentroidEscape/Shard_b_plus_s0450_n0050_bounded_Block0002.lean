import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0460
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0461
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0462
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0463
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0464

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0461.inputData=Step0460.endpointData := by decide +kernel

theorem glue1 : Step0462.inputData=Step0461.endpointData := by decide +kernel

theorem glue2 : Step0463.inputData=Step0462.endpointData := by decide +kernel

theorem glue3 : Step0464.inputData=Step0463.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0460.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0464.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0460.stepData
  | 1=>Step0461.stepData
  | 2=>Step0462.stepData
  | 3=>Step0463.stepData
  | 4=>Step0464.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0460.stepData=true ∧
      (∀ i : Fin 7, Step0461.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0460.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0460.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0460.allStagesChecked,?_,Step0460.initialMarginCheck⟩
    intro i
    rw [Step0461.inputCoefficient,← Step0460.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0461.stepData=true ∧
      (∀ i : Fin 7, Step0462.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0461.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0461.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0461.allStagesChecked,?_,Step0461.initialMarginCheck⟩
    intro i
    rw [Step0462.inputCoefficient,← Step0461.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0462.stepData=true ∧
      (∀ i : Fin 7, Step0463.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0462.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0462.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0462.allStagesChecked,?_,Step0462.initialMarginCheck⟩
    intro i
    rw [Step0463.inputCoefficient,← Step0462.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0463.stepData=true ∧
      (∀ i : Fin 7, Step0464.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0463.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0463.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0463.allStagesChecked,?_,Step0463.initialMarginCheck⟩
    intro i
    rw [Step0464.inputCoefficient,← Step0463.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0464.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0464.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0464.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0464.allStagesChecked,?_,Step0464.initialMarginCheck⟩
    intro i
    change Step0464.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0464.stepData)[i.val]
    rw [← Step0464.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0460.stepData.coefficient 0 i=Step0460.inputData[i.val]
  exact Step0460.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Block0002
