import Lemniscate.CircleClassicalJetAlgebra
import Lemniscate.PeriodicSobolevClassicalJet
import Lemniscate.PeriodicSmoothClassicalJet

/-! Actual spatial jets of the physical derivatives of a Sobolev height.
The jet-algebra directions differentiate the circle coordinate x; only the
outer physical derivative j carries the factor (sqrt 2)^j. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ContDiff

variable (T : ℝ) [Fact (0 < T)]

def circleSobolevPhysicalJetLift (m : ℕ) :
    CircleSobolevSpace T (m+5) →L[ℂ] (Fin 5 → CircleClassicalJetAlgebra T m) :=
  ContinuousLinearMap.pi fun j =>
    (circleClassicalJetPack T m).comp
      (ContinuousLinearMap.pi fun i : Fin (m+1) =>
        ((((Real.sqrt 2)^j.val:ℝ):ℂ) •
          ((ContinuousLinearMap.proj ⟨j.val+i.val,by omega⟩).comp
            (circleSobolevClassicalJet T (m+4)))))

theorem circle_sobolev_physical_jet_lift_apply (m : ℕ)
    (f : CircleSobolevSpace T (m+5)) (j : Fin 5) :
    circleSobolevPhysicalJetLift T m f j =
      circleClassicalJetPack T m (fun i : Fin (m+1) =>
        (((Real.sqrt 2)^j.val:ℝ):ℂ) •
          circleSobolevClassicalJet T (m+4) f ⟨j.val+i.val,by omega⟩) := rfl

theorem circle_sobolev_physical_jet_lift_holonomic (m : ℕ)
    (f : CircleSobolevSpace T (m+5)) (j : Fin 5) :
    CircleClassicalJetHolonomic T m (circleSobolevPhysicalJetLift T m f j) := by
  rw [circle_sobolev_physical_jet_lift_apply]
  apply circle_classical_jet_pack_holonomic
  intro i
  let k : Fin (m+4) := ⟨j.val+i.val,by omega⟩
  have hd := circle_sobolev_classical_jet_deriv T (m+4) f k
  intro x
  simpa only [ContinuousMap.smul_apply] using!
    (hd x).const_smul ((((Real.sqrt 2)^j.val:ℝ):ℂ))

theorem circle_sobolev_physical_jet_lift_value (m : ℕ)
    (f : CircleSobolevSpace T (m+5)) (j : Fin 5) :
    circleClassicalJetValue T m (circleSobolevPhysicalJetLift T m f j) =
      (((Real.sqrt 2)^j.val:ℝ):ℂ) •
        circleSobolevClassicalJet T (m+4) f (j.castLE (by omega : 5≤m+5)) := by
  rw [circle_sobolev_physical_jet_lift_apply,circle_classical_jet_pack_value]
  rfl

/-- A smooth circle coefficient has an actual holonomic jet of every
order, with exactly its original continuous value. -/
theorem circle_classical_jet_lift_of_smooth
    (m : ℕ) (f : C(AddCircle T,ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle T))) :
    ∃ z : CircleClassicalJetAlgebra T m, CircleClassicalJetHolonomic T m z ∧
      circleClassicalJetValue T m z = f := by
  have hp : Function.Periodic (fun x : ℝ => f (x : AddCircle T)) T := by
    intro x
    exact congrArg f (AddCircle.coe_add_period T x)
  obtain ⟨F,hF,hD⟩ := periodic_smooth_classical_jet T
    (fun x : ℝ => f (x : AddCircle T)) hf hp
  let z := circleClassicalJetPack T m (fun i : Fin (m+1) => F i.val)
  refine ⟨z,?_,?_⟩
  · exact circle_classical_jet_pack_holonomic T m _ (fun i => hD i.val)
  · apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    change circleClassicalJetValue T m (circleClassicalJetPack T m
      (fun i : Fin (m+1) => F i.val)) (x : AddCircle T) = f (x : AddCircle T)
    rw [circle_classical_jet_pack_value]
    simpa only [Fin.val_zero,iteratedDeriv_zero] using hF 0 x

end Lemniscate
