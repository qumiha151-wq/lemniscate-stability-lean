import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0455
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0456
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0457
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0458
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0459

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0456.inputData=Step0455.endpointData := by decide +kernel

theorem glue1 : Step0457.inputData=Step0456.endpointData := by decide +kernel

theorem glue2 : Step0458.inputData=Step0457.endpointData := by decide +kernel

theorem glue3 : Step0459.inputData=Step0458.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0455.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0459.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0455.stepData
  | 1=>Step0456.stepData
  | 2=>Step0457.stepData
  | 3=>Step0458.stepData
  | 4=>Step0459.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0455.stepData=true ∧
      (∀ i : Fin 7, Step0456.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0455.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0455.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0455.allStagesChecked,?_,Step0455.initialMarginCheck⟩
    intro i
    rw [Step0456.inputCoefficient,← Step0455.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0456.stepData=true ∧
      (∀ i : Fin 7, Step0457.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0456.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0456.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0456.allStagesChecked,?_,Step0456.initialMarginCheck⟩
    intro i
    rw [Step0457.inputCoefficient,← Step0456.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0457.stepData=true ∧
      (∀ i : Fin 7, Step0458.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0457.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0457.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0457.allStagesChecked,?_,Step0457.initialMarginCheck⟩
    intro i
    rw [Step0458.inputCoefficient,← Step0457.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0458.stepData=true ∧
      (∀ i : Fin 7, Step0459.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0458.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0458.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0458.allStagesChecked,?_,Step0458.initialMarginCheck⟩
    intro i
    rw [Step0459.inputCoefficient,← Step0458.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0459.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0459.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0459.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0459.allStagesChecked,?_,Step0459.initialMarginCheck⟩
    intro i
    change Step0459.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0459.stepData)[i.val]
    rw [← Step0459.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0455.stepData.coefficient 0 i=Step0455.inputData[i.val]
  exact Step0455.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0001
