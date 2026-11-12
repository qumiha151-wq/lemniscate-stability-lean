import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0000_n0050_bounded_Step0030
import CentroidEscape.Shard_a_minus_s0000_n0050_bounded_Step0031
import CentroidEscape.Shard_a_minus_s0000_n0050_bounded_Step0032
import CentroidEscape.Shard_a_minus_s0000_n0050_bounded_Step0033
import CentroidEscape.Shard_a_minus_s0000_n0050_bounded_Step0034

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0000_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0031.inputData=Step0030.endpointData := by decide +kernel

theorem glue1 : Step0032.inputData=Step0031.endpointData := by decide +kernel

theorem glue2 : Step0033.inputData=Step0032.endpointData := by decide +kernel

theorem glue3 : Step0034.inputData=Step0033.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0030.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0034.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0030.stepData
  | 1=>Step0031.stepData
  | 2=>Step0032.stepData
  | 3=>Step0033.stepData
  | 4=>Step0034.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0030.stepData=true ∧
      (∀ i : Fin 7, Step0031.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0030.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0030.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0030.allStagesChecked,?_,Step0030.initialMarginCheck⟩
    intro i
    rw [Step0031.inputCoefficient,← Step0030.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0031.stepData=true ∧
      (∀ i : Fin 7, Step0032.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0031.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0031.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0031.allStagesChecked,?_,Step0031.initialMarginCheck⟩
    intro i
    rw [Step0032.inputCoefficient,← Step0031.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0032.stepData=true ∧
      (∀ i : Fin 7, Step0033.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0032.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0032.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0032.allStagesChecked,?_,Step0032.initialMarginCheck⟩
    intro i
    rw [Step0033.inputCoefficient,← Step0032.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0033.stepData=true ∧
      (∀ i : Fin 7, Step0034.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0033.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0033.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0033.allStagesChecked,?_,Step0033.initialMarginCheck⟩
    intro i
    rw [Step0034.inputCoefficient,← Step0033.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0034.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0034.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0034.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0034.allStagesChecked,?_,Step0034.initialMarginCheck⟩
    intro i
    change Step0034.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0034.stepData)[i.val]
    rw [← Step0034.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0030.stepData.coefficient 0 i=Step0030.inputData[i.val]
  exact Step0030.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0000_n0050_bounded.Block0006
