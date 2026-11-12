import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0580
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0581
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0582
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0583
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Step0584

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0581.inputData=Step0580.endpointData := by decide +kernel

theorem glue1 : Step0582.inputData=Step0581.endpointData := by decide +kernel

theorem glue2 : Step0583.inputData=Step0582.endpointData := by decide +kernel

theorem glue3 : Step0584.inputData=Step0583.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0580.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0584.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0580.stepData
  | 1=>Step0581.stepData
  | 2=>Step0582.stepData
  | 3=>Step0583.stepData
  | 4=>Step0584.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0580.stepData=true ∧
      (∀ i : Fin 7, Step0581.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0580.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0580.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0580.allStagesChecked,?_,Step0580.initialMarginCheck⟩
    intro i
    rw [Step0581.inputCoefficient,← Step0580.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0581.stepData=true ∧
      (∀ i : Fin 7, Step0582.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0581.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0581.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0581.allStagesChecked,?_,Step0581.initialMarginCheck⟩
    intro i
    rw [Step0582.inputCoefficient,← Step0581.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0582.stepData=true ∧
      (∀ i : Fin 7, Step0583.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0582.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0582.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0582.allStagesChecked,?_,Step0582.initialMarginCheck⟩
    intro i
    rw [Step0583.inputCoefficient,← Step0582.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0583.stepData=true ∧
      (∀ i : Fin 7, Step0584.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0583.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0583.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0583.allStagesChecked,?_,Step0583.initialMarginCheck⟩
    intro i
    rw [Step0584.inputCoefficient,← Step0583.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0584.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0584.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0584.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0584.allStagesChecked,?_,Step0584.initialMarginCheck⟩
    intro i
    change Step0584.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0584.stepData)[i.val]
    rw [← Step0584.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0580.stepData.coefficient 0 i=Step0580.inputData[i.val]
  exact Step0580.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Block0006
