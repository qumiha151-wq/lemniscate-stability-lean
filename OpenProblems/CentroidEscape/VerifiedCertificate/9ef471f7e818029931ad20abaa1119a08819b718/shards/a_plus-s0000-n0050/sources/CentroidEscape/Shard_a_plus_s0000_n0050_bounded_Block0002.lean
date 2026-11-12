import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0010
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0011
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0012
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0013
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0014

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0011.inputData=Step0010.endpointData := by decide +kernel

theorem glue1 : Step0012.inputData=Step0011.endpointData := by decide +kernel

theorem glue2 : Step0013.inputData=Step0012.endpointData := by decide +kernel

theorem glue3 : Step0014.inputData=Step0013.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0010.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0014.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0010.stepData
  | 1=>Step0011.stepData
  | 2=>Step0012.stepData
  | 3=>Step0013.stepData
  | 4=>Step0014.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0010.stepData=true ∧
      (∀ i : Fin 7, Step0011.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0010.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0010.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0010.allStagesChecked,?_,Step0010.initialMarginCheck⟩
    intro i
    rw [Step0011.inputCoefficient,← Step0010.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0011.stepData=true ∧
      (∀ i : Fin 7, Step0012.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0011.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0011.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0011.allStagesChecked,?_,Step0011.initialMarginCheck⟩
    intro i
    rw [Step0012.inputCoefficient,← Step0011.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0012.stepData=true ∧
      (∀ i : Fin 7, Step0013.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0012.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0012.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0012.allStagesChecked,?_,Step0012.initialMarginCheck⟩
    intro i
    rw [Step0013.inputCoefficient,← Step0012.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0013.stepData=true ∧
      (∀ i : Fin 7, Step0014.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0013.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0013.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0013.allStagesChecked,?_,Step0013.initialMarginCheck⟩
    intro i
    rw [Step0014.inputCoefficient,← Step0013.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0014.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0014.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0014.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0014.allStagesChecked,?_,Step0014.initialMarginCheck⟩
    intro i
    change Step0014.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0014.stepData)[i.val]
    rw [← Step0014.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0010.stepData.coefficient 0 i=Step0010.inputData[i.val]
  exact Step0010.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0002
