import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0125
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0126
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0127
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0128
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0129

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0126.inputData=Step0125.endpointData := by decide +kernel

theorem glue1 : Step0127.inputData=Step0126.endpointData := by decide +kernel

theorem glue2 : Step0128.inputData=Step0127.endpointData := by decide +kernel

theorem glue3 : Step0129.inputData=Step0128.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0125.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0129.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0125.stepData
  | 1=>Step0126.stepData
  | 2=>Step0127.stepData
  | 3=>Step0128.stepData
  | 4=>Step0129.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0125.stepData=true ∧
      (∀ i : Fin 7, Step0126.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0125.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0125.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0125.allStagesChecked,?_,Step0125.initialMarginCheck⟩
    intro i
    rw [Step0126.inputCoefficient,← Step0125.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0126.stepData=true ∧
      (∀ i : Fin 7, Step0127.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0126.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0126.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0126.allStagesChecked,?_,Step0126.initialMarginCheck⟩
    intro i
    rw [Step0127.inputCoefficient,← Step0126.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0127.stepData=true ∧
      (∀ i : Fin 7, Step0128.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0127.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0127.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0127.allStagesChecked,?_,Step0127.initialMarginCheck⟩
    intro i
    rw [Step0128.inputCoefficient,← Step0127.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0128.stepData=true ∧
      (∀ i : Fin 7, Step0129.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0128.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0128.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0128.allStagesChecked,?_,Step0128.initialMarginCheck⟩
    intro i
    rw [Step0129.inputCoefficient,← Step0128.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0129.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0129.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0129.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0129.allStagesChecked,?_,Step0129.initialMarginCheck⟩
    intro i
    change Step0129.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0129.stepData)[i.val]
    rw [← Step0129.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0125.stepData.coefficient 0 i=Step0125.inputData[i.val]
  exact Step0125.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Block0005
