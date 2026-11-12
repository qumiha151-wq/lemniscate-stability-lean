import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0270
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0271
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0272
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0273
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0274

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0271.inputData=Step0270.endpointData := by decide +kernel

theorem glue1 : Step0272.inputData=Step0271.endpointData := by decide +kernel

theorem glue2 : Step0273.inputData=Step0272.endpointData := by decide +kernel

theorem glue3 : Step0274.inputData=Step0273.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0270.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0274.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0270.stepData
  | 1=>Step0271.stepData
  | 2=>Step0272.stepData
  | 3=>Step0273.stepData
  | 4=>Step0274.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0270.stepData=true ∧
      (∀ i : Fin 7, Step0271.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0270.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0270.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0270.allStagesChecked,?_,Step0270.initialMarginCheck⟩
    intro i
    rw [Step0271.inputCoefficient,← Step0270.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0271.stepData=true ∧
      (∀ i : Fin 7, Step0272.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0271.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0271.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0271.allStagesChecked,?_,Step0271.initialMarginCheck⟩
    intro i
    rw [Step0272.inputCoefficient,← Step0271.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0272.stepData=true ∧
      (∀ i : Fin 7, Step0273.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0272.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0272.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0272.allStagesChecked,?_,Step0272.initialMarginCheck⟩
    intro i
    rw [Step0273.inputCoefficient,← Step0272.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0273.stepData=true ∧
      (∀ i : Fin 7, Step0274.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0273.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0273.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0273.allStagesChecked,?_,Step0273.initialMarginCheck⟩
    intro i
    rw [Step0274.inputCoefficient,← Step0273.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0274.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0274.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0274.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0274.allStagesChecked,?_,Step0274.initialMarginCheck⟩
    intro i
    change Step0274.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0274.stepData)[i.val]
    rw [← Step0274.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0270.stepData.coefficient 0 i=Step0270.inputData[i.val]
  exact Step0270.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0004
