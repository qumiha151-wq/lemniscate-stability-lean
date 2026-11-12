import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0525
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0526
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0527
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0528
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0529

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0526.inputData=Step0525.endpointData := by decide +kernel

theorem glue1 : Step0527.inputData=Step0526.endpointData := by decide +kernel

theorem glue2 : Step0528.inputData=Step0527.endpointData := by decide +kernel

theorem glue3 : Step0529.inputData=Step0528.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0525.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0529.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0525.stepData
  | 1=>Step0526.stepData
  | 2=>Step0527.stepData
  | 3=>Step0528.stepData
  | 4=>Step0529.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0525.stepData=true ∧
      (∀ i : Fin 7, Step0526.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0525.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0525.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0525.allStagesChecked,?_,Step0525.initialMarginCheck⟩
    intro i
    rw [Step0526.inputCoefficient,← Step0525.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0526.stepData=true ∧
      (∀ i : Fin 7, Step0527.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0526.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0526.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0526.allStagesChecked,?_,Step0526.initialMarginCheck⟩
    intro i
    rw [Step0527.inputCoefficient,← Step0526.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0527.stepData=true ∧
      (∀ i : Fin 7, Step0528.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0527.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0527.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0527.allStagesChecked,?_,Step0527.initialMarginCheck⟩
    intro i
    rw [Step0528.inputCoefficient,← Step0527.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0528.stepData=true ∧
      (∀ i : Fin 7, Step0529.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0528.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0528.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0528.allStagesChecked,?_,Step0528.initialMarginCheck⟩
    intro i
    rw [Step0529.inputCoefficient,← Step0528.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0529.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0529.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0529.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0529.allStagesChecked,?_,Step0529.initialMarginCheck⟩
    intro i
    change Step0529.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0529.stepData)[i.val]
    rw [← Step0529.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0525.stepData.coefficient 0 i=Step0525.inputData[i.val]
  exact Step0525.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Block0005
