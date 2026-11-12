import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0180
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0181
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0182
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0183
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0184

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0181.inputData=Step0180.endpointData := by decide +kernel

theorem glue1 : Step0182.inputData=Step0181.endpointData := by decide +kernel

theorem glue2 : Step0183.inputData=Step0182.endpointData := by decide +kernel

theorem glue3 : Step0184.inputData=Step0183.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0180.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0184.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0180.stepData
  | 1=>Step0181.stepData
  | 2=>Step0182.stepData
  | 3=>Step0183.stepData
  | 4=>Step0184.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0180.stepData=true ∧
      (∀ i : Fin 7, Step0181.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0180.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0180.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0180.allStagesChecked,?_,Step0180.initialMarginCheck⟩
    intro i
    rw [Step0181.inputCoefficient,← Step0180.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0181.stepData=true ∧
      (∀ i : Fin 7, Step0182.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0181.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0181.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0181.allStagesChecked,?_,Step0181.initialMarginCheck⟩
    intro i
    rw [Step0182.inputCoefficient,← Step0181.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0182.stepData=true ∧
      (∀ i : Fin 7, Step0183.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0182.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0182.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0182.allStagesChecked,?_,Step0182.initialMarginCheck⟩
    intro i
    rw [Step0183.inputCoefficient,← Step0182.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0183.stepData=true ∧
      (∀ i : Fin 7, Step0184.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0183.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0183.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0183.allStagesChecked,?_,Step0183.initialMarginCheck⟩
    intro i
    rw [Step0184.inputCoefficient,← Step0183.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0184.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0184.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0184.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0184.allStagesChecked,?_,Step0184.initialMarginCheck⟩
    intro i
    change Step0184.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0184.stepData)[i.val]
    rw [← Step0184.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0180.stepData.coefficient 0 i=Step0180.inputData[i.val]
  exact Step0180.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Block0006
