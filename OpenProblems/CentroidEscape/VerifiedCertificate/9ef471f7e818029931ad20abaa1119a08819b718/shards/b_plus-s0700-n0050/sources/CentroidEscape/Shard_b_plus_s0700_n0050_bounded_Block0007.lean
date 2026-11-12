import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0735
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0736
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0737
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0738
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0739

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0736.inputData=Step0735.endpointData := by decide +kernel

theorem glue1 : Step0737.inputData=Step0736.endpointData := by decide +kernel

theorem glue2 : Step0738.inputData=Step0737.endpointData := by decide +kernel

theorem glue3 : Step0739.inputData=Step0738.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0735.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0739.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0735.stepData
  | 1=>Step0736.stepData
  | 2=>Step0737.stepData
  | 3=>Step0738.stepData
  | 4=>Step0739.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0735.stepData=true ∧
      (∀ i : Fin 7, Step0736.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0735.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0735.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0735.allStagesChecked,?_,Step0735.initialMarginCheck⟩
    intro i
    rw [Step0736.inputCoefficient,← Step0735.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0736.stepData=true ∧
      (∀ i : Fin 7, Step0737.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0736.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0736.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0736.allStagesChecked,?_,Step0736.initialMarginCheck⟩
    intro i
    rw [Step0737.inputCoefficient,← Step0736.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0737.stepData=true ∧
      (∀ i : Fin 7, Step0738.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0737.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0737.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0737.allStagesChecked,?_,Step0737.initialMarginCheck⟩
    intro i
    rw [Step0738.inputCoefficient,← Step0737.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0738.stepData=true ∧
      (∀ i : Fin 7, Step0739.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0738.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0738.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0738.allStagesChecked,?_,Step0738.initialMarginCheck⟩
    intro i
    rw [Step0739.inputCoefficient,← Step0738.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0739.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0739.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0739.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0739.allStagesChecked,?_,Step0739.initialMarginCheck⟩
    intro i
    change Step0739.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0739.stepData)[i.val]
    rw [← Step0739.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0735.stepData.coefficient 0 i=Step0735.inputData[i.val]
  exact Step0735.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Block0007
