import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0365
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0366
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0367
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0368
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0369

namespace CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0366.inputData=Step0365.endpointData := by decide +kernel

theorem glue1 : Step0367.inputData=Step0366.endpointData := by decide +kernel

theorem glue2 : Step0368.inputData=Step0367.endpointData := by decide +kernel

theorem glue3 : Step0369.inputData=Step0368.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0365.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0369.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0365.stepData
  | 1=>Step0366.stepData
  | 2=>Step0367.stepData
  | 3=>Step0368.stepData
  | 4=>Step0369.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0365.stepData=true ∧
      (∀ i : Fin 7, Step0366.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0365.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0365.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0365.allStagesChecked,?_,Step0365.initialMarginCheck⟩
    intro i
    rw [Step0366.inputCoefficient,← Step0365.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0366.stepData=true ∧
      (∀ i : Fin 7, Step0367.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0366.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0366.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0366.allStagesChecked,?_,Step0366.initialMarginCheck⟩
    intro i
    rw [Step0367.inputCoefficient,← Step0366.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0367.stepData=true ∧
      (∀ i : Fin 7, Step0368.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0367.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0367.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0367.allStagesChecked,?_,Step0367.initialMarginCheck⟩
    intro i
    rw [Step0368.inputCoefficient,← Step0367.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0368.stepData=true ∧
      (∀ i : Fin 7, Step0369.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0368.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0368.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0368.allStagesChecked,?_,Step0368.initialMarginCheck⟩
    intro i
    rw [Step0369.inputCoefficient,← Step0368.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0369.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0369.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0369.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0369.allStagesChecked,?_,Step0369.initialMarginCheck⟩
    intro i
    change Step0369.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0369.stepData)[i.val]
    rw [← Step0369.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0365.stepData.coefficient 0 i=Step0365.inputData[i.val]
  exact Step0365.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0003
