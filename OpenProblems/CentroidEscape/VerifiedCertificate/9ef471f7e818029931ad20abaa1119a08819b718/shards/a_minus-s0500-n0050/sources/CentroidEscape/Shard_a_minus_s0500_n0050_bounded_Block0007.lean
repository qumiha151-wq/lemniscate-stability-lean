import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0500_n0050_bounded_Step0535
import CentroidEscape.Shard_a_minus_s0500_n0050_bounded_Step0536
import CentroidEscape.Shard_a_minus_s0500_n0050_bounded_Step0537
import CentroidEscape.Shard_a_minus_s0500_n0050_bounded_Step0538
import CentroidEscape.Shard_a_minus_s0500_n0050_bounded_Step0539

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0536.inputData=Step0535.endpointData := by decide +kernel

theorem glue1 : Step0537.inputData=Step0536.endpointData := by decide +kernel

theorem glue2 : Step0538.inputData=Step0537.endpointData := by decide +kernel

theorem glue3 : Step0539.inputData=Step0538.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0535.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0539.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0535.stepData
  | 1=>Step0536.stepData
  | 2=>Step0537.stepData
  | 3=>Step0538.stepData
  | 4=>Step0539.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0535.stepData=true ∧
      (∀ i : Fin 7, Step0536.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0535.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0535.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0535.allStagesChecked,?_,Step0535.initialMarginCheck⟩
    intro i
    rw [Step0536.inputCoefficient,← Step0535.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0536.stepData=true ∧
      (∀ i : Fin 7, Step0537.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0536.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0536.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0536.allStagesChecked,?_,Step0536.initialMarginCheck⟩
    intro i
    rw [Step0537.inputCoefficient,← Step0536.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0537.stepData=true ∧
      (∀ i : Fin 7, Step0538.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0537.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0537.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0537.allStagesChecked,?_,Step0537.initialMarginCheck⟩
    intro i
    rw [Step0538.inputCoefficient,← Step0537.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0538.stepData=true ∧
      (∀ i : Fin 7, Step0539.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0538.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0538.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0538.allStagesChecked,?_,Step0538.initialMarginCheck⟩
    intro i
    rw [Step0539.inputCoefficient,← Step0538.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0539.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0539.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0539.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0539.allStagesChecked,?_,Step0539.initialMarginCheck⟩
    intro i
    change Step0539.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0539.stepData)[i.val]
    rw [← Step0539.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0535.stepData.coefficient 0 i=Step0535.inputData[i.val]
  exact Step0535.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Block0007
