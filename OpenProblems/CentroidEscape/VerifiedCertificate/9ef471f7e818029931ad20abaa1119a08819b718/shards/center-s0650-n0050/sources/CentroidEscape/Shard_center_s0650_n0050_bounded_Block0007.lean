import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0685
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0686
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0687
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0688
import CentroidEscape.Shard_center_s0650_n0050_bounded_Step0689

namespace CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0686.inputData=Step0685.endpointData := by decide +kernel

theorem glue1 : Step0687.inputData=Step0686.endpointData := by decide +kernel

theorem glue2 : Step0688.inputData=Step0687.endpointData := by decide +kernel

theorem glue3 : Step0689.inputData=Step0688.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0685.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0689.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0685.stepData
  | 1=>Step0686.stepData
  | 2=>Step0687.stepData
  | 3=>Step0688.stepData
  | 4=>Step0689.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0685.stepData=true ∧
      (∀ i : Fin 7, Step0686.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0685.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0685.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0685.allStagesChecked,?_,Step0685.initialMarginCheck⟩
    intro i
    rw [Step0686.inputCoefficient,← Step0685.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0686.stepData=true ∧
      (∀ i : Fin 7, Step0687.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0686.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0686.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0686.allStagesChecked,?_,Step0686.initialMarginCheck⟩
    intro i
    rw [Step0687.inputCoefficient,← Step0686.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0687.stepData=true ∧
      (∀ i : Fin 7, Step0688.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0687.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0687.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0687.allStagesChecked,?_,Step0687.initialMarginCheck⟩
    intro i
    rw [Step0688.inputCoefficient,← Step0687.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0688.stepData=true ∧
      (∀ i : Fin 7, Step0689.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0688.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0688.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0688.allStagesChecked,?_,Step0688.initialMarginCheck⟩
    intro i
    rw [Step0689.inputCoefficient,← Step0688.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0689.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0689.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0689.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0689.allStagesChecked,?_,Step0689.initialMarginCheck⟩
    intro i
    change Step0689.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0689.stepData)[i.val]
    rw [← Step0689.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0685.stepData.coefficient 0 i=Step0685.inputData[i.val]
  exact Step0685.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Block0007
