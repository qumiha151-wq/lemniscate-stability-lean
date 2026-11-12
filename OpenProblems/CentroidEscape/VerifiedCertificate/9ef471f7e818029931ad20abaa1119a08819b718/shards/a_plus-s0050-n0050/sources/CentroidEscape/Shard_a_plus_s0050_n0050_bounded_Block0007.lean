import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0085
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0086
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0087
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0088
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0089

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0050_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0086.inputData=Step0085.endpointData := by decide +kernel

theorem glue1 : Step0087.inputData=Step0086.endpointData := by decide +kernel

theorem glue2 : Step0088.inputData=Step0087.endpointData := by decide +kernel

theorem glue3 : Step0089.inputData=Step0088.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0085.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0089.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0085.stepData
  | 1=>Step0086.stepData
  | 2=>Step0087.stepData
  | 3=>Step0088.stepData
  | 4=>Step0089.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0085.stepData=true ∧
      (∀ i : Fin 7, Step0086.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0085.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0085.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0085.allStagesChecked,?_,Step0085.initialMarginCheck⟩
    intro i
    rw [Step0086.inputCoefficient,← Step0085.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0086.stepData=true ∧
      (∀ i : Fin 7, Step0087.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0086.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0086.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0086.allStagesChecked,?_,Step0086.initialMarginCheck⟩
    intro i
    rw [Step0087.inputCoefficient,← Step0086.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0087.stepData=true ∧
      (∀ i : Fin 7, Step0088.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0087.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0087.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0087.allStagesChecked,?_,Step0087.initialMarginCheck⟩
    intro i
    rw [Step0088.inputCoefficient,← Step0087.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0088.stepData=true ∧
      (∀ i : Fin 7, Step0089.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0088.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0088.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0088.allStagesChecked,?_,Step0088.initialMarginCheck⟩
    intro i
    rw [Step0089.inputCoefficient,← Step0088.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0089.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0089.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0089.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0089.allStagesChecked,?_,Step0089.initialMarginCheck⟩
    intro i
    change Step0089.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0089.stepData)[i.val]
    rw [← Step0089.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0085.stepData.coefficient 0 i=Step0085.inputData[i.val]
  exact Step0085.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0050_n0050_bounded.Block0007
