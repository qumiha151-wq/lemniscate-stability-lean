import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0000
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0001
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0002
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0003
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Step0004

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0001.inputData=Step0000.endpointData := by decide +kernel

theorem glue1 : Step0002.inputData=Step0001.endpointData := by decide +kernel

theorem glue2 : Step0003.inputData=Step0002.endpointData := by decide +kernel

theorem glue3 : Step0004.inputData=Step0003.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0004.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0000.stepData
  | 1=>Step0001.stepData
  | 2=>Step0002.stepData
  | 3=>Step0003.stepData
  | 4=>Step0004.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0000.stepData=true ∧
      (∀ i : Fin 7, Step0001.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0000.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0000.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0000.allStagesChecked,?_,Step0000.initialMarginCheck⟩
    intro i
    rw [Step0001.inputCoefficient,← Step0000.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0001.stepData=true ∧
      (∀ i : Fin 7, Step0002.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0001.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0001.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0001.allStagesChecked,?_,Step0001.initialMarginCheck⟩
    intro i
    rw [Step0002.inputCoefficient,← Step0001.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0002.stepData=true ∧
      (∀ i : Fin 7, Step0003.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0002.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0002.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0002.allStagesChecked,?_,Step0002.initialMarginCheck⟩
    intro i
    rw [Step0003.inputCoefficient,← Step0002.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0003.stepData=true ∧
      (∀ i : Fin 7, Step0004.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0003.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0003.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0003.allStagesChecked,?_,Step0003.initialMarginCheck⟩
    intro i
    rw [Step0004.inputCoefficient,← Step0003.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0004.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0004.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0004.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0004.allStagesChecked,?_,Step0004.initialMarginCheck⟩
    intro i
    change Step0004.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0004.stepData)[i.val]
    rw [← Step0004.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0000.stepData.coefficient 0 i=Step0000.inputData[i.val]
  exact Step0000.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Block0000
