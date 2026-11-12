import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0020
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0021
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0022
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0023
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0024

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0021.inputData=Step0020.endpointData := by decide +kernel

theorem glue1 : Step0022.inputData=Step0021.endpointData := by decide +kernel

theorem glue2 : Step0023.inputData=Step0022.endpointData := by decide +kernel

theorem glue3 : Step0024.inputData=Step0023.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0020.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0024.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0020.stepData
  | 1=>Step0021.stepData
  | 2=>Step0022.stepData
  | 3=>Step0023.stepData
  | 4=>Step0024.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0020.stepData=true ∧
      (∀ i : Fin 7, Step0021.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0020.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0020.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0020.allStagesChecked,?_,Step0020.initialMarginCheck⟩
    intro i
    rw [Step0021.inputCoefficient,← Step0020.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0021.stepData=true ∧
      (∀ i : Fin 7, Step0022.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0021.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0021.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0021.allStagesChecked,?_,Step0021.initialMarginCheck⟩
    intro i
    rw [Step0022.inputCoefficient,← Step0021.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0022.stepData=true ∧
      (∀ i : Fin 7, Step0023.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0022.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0022.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0022.allStagesChecked,?_,Step0022.initialMarginCheck⟩
    intro i
    rw [Step0023.inputCoefficient,← Step0022.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0023.stepData=true ∧
      (∀ i : Fin 7, Step0024.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0023.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0023.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0023.allStagesChecked,?_,Step0023.initialMarginCheck⟩
    intro i
    rw [Step0024.inputCoefficient,← Step0023.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0024.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0024.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0024.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0024.allStagesChecked,?_,Step0024.initialMarginCheck⟩
    intro i
    change Step0024.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0024.stepData)[i.val]
    rw [← Step0024.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0020.stepData.coefficient 0 i=Step0020.inputData[i.val]
  exact Step0020.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0004
