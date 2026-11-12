import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0035
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0036
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0037
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0038
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0039

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0036.inputData=Step0035.endpointData := by decide +kernel

theorem glue1 : Step0037.inputData=Step0036.endpointData := by decide +kernel

theorem glue2 : Step0038.inputData=Step0037.endpointData := by decide +kernel

theorem glue3 : Step0039.inputData=Step0038.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0035.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0039.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0035.stepData
  | 1=>Step0036.stepData
  | 2=>Step0037.stepData
  | 3=>Step0038.stepData
  | 4=>Step0039.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0035.stepData=true ∧
      (∀ i : Fin 7, Step0036.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0035.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0035.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0035.allStagesChecked,?_,Step0035.initialMarginCheck⟩
    intro i
    rw [Step0036.inputCoefficient,← Step0035.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0036.stepData=true ∧
      (∀ i : Fin 7, Step0037.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0036.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0036.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0036.allStagesChecked,?_,Step0036.initialMarginCheck⟩
    intro i
    rw [Step0037.inputCoefficient,← Step0036.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0037.stepData=true ∧
      (∀ i : Fin 7, Step0038.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0037.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0037.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0037.allStagesChecked,?_,Step0037.initialMarginCheck⟩
    intro i
    rw [Step0038.inputCoefficient,← Step0037.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0038.stepData=true ∧
      (∀ i : Fin 7, Step0039.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0038.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0038.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0038.allStagesChecked,?_,Step0038.initialMarginCheck⟩
    intro i
    rw [Step0039.inputCoefficient,← Step0038.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0039.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0039.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0039.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0039.allStagesChecked,?_,Step0039.initialMarginCheck⟩
    intro i
    change Step0039.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0039.stepData)[i.val]
    rw [← Step0039.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0035.stepData.coefficient 0 i=Step0035.inputData[i.val]
  exact Step0035.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0007
