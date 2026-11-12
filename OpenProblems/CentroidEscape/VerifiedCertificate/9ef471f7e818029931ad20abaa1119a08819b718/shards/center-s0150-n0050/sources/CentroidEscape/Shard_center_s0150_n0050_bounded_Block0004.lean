import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0170
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0171
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0172
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0173
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0174

namespace CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0171.inputData=Step0170.endpointData := by decide +kernel

theorem glue1 : Step0172.inputData=Step0171.endpointData := by decide +kernel

theorem glue2 : Step0173.inputData=Step0172.endpointData := by decide +kernel

theorem glue3 : Step0174.inputData=Step0173.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0170.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0174.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0170.stepData
  | 1=>Step0171.stepData
  | 2=>Step0172.stepData
  | 3=>Step0173.stepData
  | 4=>Step0174.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0170.stepData=true ∧
      (∀ i : Fin 7, Step0171.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0170.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0170.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0170.allStagesChecked,?_,Step0170.initialMarginCheck⟩
    intro i
    rw [Step0171.inputCoefficient,← Step0170.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0171.stepData=true ∧
      (∀ i : Fin 7, Step0172.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0171.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0171.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0171.allStagesChecked,?_,Step0171.initialMarginCheck⟩
    intro i
    rw [Step0172.inputCoefficient,← Step0171.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0172.stepData=true ∧
      (∀ i : Fin 7, Step0173.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0172.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0172.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0172.allStagesChecked,?_,Step0172.initialMarginCheck⟩
    intro i
    rw [Step0173.inputCoefficient,← Step0172.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0173.stepData=true ∧
      (∀ i : Fin 7, Step0174.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0173.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0173.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0173.allStagesChecked,?_,Step0173.initialMarginCheck⟩
    intro i
    rw [Step0174.inputCoefficient,← Step0173.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0174.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0174.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0174.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0174.allStagesChecked,?_,Step0174.initialMarginCheck⟩
    intro i
    change Step0174.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0174.stepData)[i.val]
    rw [← Step0174.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0170.stepData.coefficient 0 i=Step0170.inputData[i.val]
  exact Step0170.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0004
