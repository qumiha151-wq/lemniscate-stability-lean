import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0545
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0546
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0547
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0548
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0549

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0546.inputData=Step0545.endpointData := by decide +kernel

theorem glue1 : Step0547.inputData=Step0546.endpointData := by decide +kernel

theorem glue2 : Step0548.inputData=Step0547.endpointData := by decide +kernel

theorem glue3 : Step0549.inputData=Step0548.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0545.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0549.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0545.stepData
  | 1=>Step0546.stepData
  | 2=>Step0547.stepData
  | 3=>Step0548.stepData
  | 4=>Step0549.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0545.stepData=true ∧
      (∀ i : Fin 7, Step0546.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0545.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0545.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0545.allStagesChecked,?_,Step0545.initialMarginCheck⟩
    intro i
    rw [Step0546.inputCoefficient,← Step0545.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0546.stepData=true ∧
      (∀ i : Fin 7, Step0547.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0546.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0546.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0546.allStagesChecked,?_,Step0546.initialMarginCheck⟩
    intro i
    rw [Step0547.inputCoefficient,← Step0546.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0547.stepData=true ∧
      (∀ i : Fin 7, Step0548.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0547.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0547.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0547.allStagesChecked,?_,Step0547.initialMarginCheck⟩
    intro i
    rw [Step0548.inputCoefficient,← Step0547.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0548.stepData=true ∧
      (∀ i : Fin 7, Step0549.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0548.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0548.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0548.allStagesChecked,?_,Step0548.initialMarginCheck⟩
    intro i
    rw [Step0549.inputCoefficient,← Step0548.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0549.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0549.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0549.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0549.allStagesChecked,?_,Step0549.initialMarginCheck⟩
    intro i
    change Step0549.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0549.stepData)[i.val]
    rw [← Step0549.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0545.stepData.coefficient 0 i=Step0545.inputData[i.val]
  exact Step0545.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Block0009
