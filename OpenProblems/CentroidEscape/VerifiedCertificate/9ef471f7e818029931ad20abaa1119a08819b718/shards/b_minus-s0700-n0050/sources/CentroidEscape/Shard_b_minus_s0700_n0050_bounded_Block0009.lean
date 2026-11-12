import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0745
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0746
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0747
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0748
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0749

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0746.inputData=Step0745.endpointData := by decide +kernel

theorem glue1 : Step0747.inputData=Step0746.endpointData := by decide +kernel

theorem glue2 : Step0748.inputData=Step0747.endpointData := by decide +kernel

theorem glue3 : Step0749.inputData=Step0748.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0745.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0749.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0745.stepData
  | 1=>Step0746.stepData
  | 2=>Step0747.stepData
  | 3=>Step0748.stepData
  | 4=>Step0749.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0745.stepData=true ∧
      (∀ i : Fin 7, Step0746.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0745.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0745.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0745.allStagesChecked,?_,Step0745.initialMarginCheck⟩
    intro i
    rw [Step0746.inputCoefficient,← Step0745.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0746.stepData=true ∧
      (∀ i : Fin 7, Step0747.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0746.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0746.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0746.allStagesChecked,?_,Step0746.initialMarginCheck⟩
    intro i
    rw [Step0747.inputCoefficient,← Step0746.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0747.stepData=true ∧
      (∀ i : Fin 7, Step0748.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0747.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0747.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0747.allStagesChecked,?_,Step0747.initialMarginCheck⟩
    intro i
    rw [Step0748.inputCoefficient,← Step0747.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0748.stepData=true ∧
      (∀ i : Fin 7, Step0749.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0748.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0748.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0748.allStagesChecked,?_,Step0748.initialMarginCheck⟩
    intro i
    rw [Step0749.inputCoefficient,← Step0748.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0749.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0749.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0749.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0749.allStagesChecked,?_,Step0749.initialMarginCheck⟩
    intro i
    change Step0749.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0749.stepData)[i.val]
    rw [← Step0749.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0745.stepData.coefficient 0 i=Step0745.inputData[i.val]
  exact Step0745.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Block0009
