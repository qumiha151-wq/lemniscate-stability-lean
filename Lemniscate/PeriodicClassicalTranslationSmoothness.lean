import Lemniscate.PeriodicSobolevTranslation
import Lemniscate.PeriodicIntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.ContinuousMap.Algebra

/-! Smooth spatial translations of a genuine smooth periodic initial datum
in every integer Sobolev norm. Higher norms need only be finite. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal ContDiff

variable (T : ℝ) [Fact (0 < T)]

private def classicalShift (f : C(AddCircle T,ℂ)) : C(ℝ,C(AddCircle T,ℂ)) :=
  ContinuousMap.curry ⟨fun z : ℝ × AddCircle T => f (z.2+(z.1:AddCircle T)),
    f.continuous.comp (continuous_snd.add ((AddCircle.continuous_mk' T).comp continuous_fst))⟩

private theorem classical_shift_hasDerivAt (f f₁ : C(AddCircle T,ℂ))
    (hf : HasCircleDeriv T f f₁) (a : ℝ) :
    HasDerivAt (classicalShift T f) (classicalShift T f₁ a) a := by
  let Q := classicalShift T f
  let G := classicalShift T f₁
  have hpoint (r : ℝ) (x : AddCircle T) :
      HasDerivAt (fun b : ℝ => Q b x) (G r x) r := by
    induction x using QuotientAddGroup.induction_on
    rename_i x
    have hparam : HasDerivAt (fun b : ℝ => x+b) (1:ℝ) r := by
      simpa only [id_eq] using (hasDerivAt_id r).const_add x
    simpa only [Q,G,classicalShift,ContinuousMap.curry_apply,ContinuousMap.coe_mk,
      AddCircle.coe_add,one_smul] using! (hf (x+r)).scomp r hparam
  have hprimitive (b : ℝ) : Q b-Q 0 = ∫ r in (0:ℝ)..b, G r := by
    apply ContinuousMap.ext
    intro x
    have heval : (∫ r in (0:ℝ)..b, G r) x = ∫ r in (0:ℝ)..b, G r x :=
      ((ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm
        (G.continuous.intervalIntegrable 0 b)).symm
    change Q b x-Q 0 x = (∫ r in (0:ℝ)..b, G r) x
    rw [heval]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hpoint r x)
      (((ContinuousMap.evalCLM ℂ x).continuous.comp G.continuous).intervalIntegrable 0 b)).symm
  have heq : (Q : ℝ → C(AddCircle T,ℂ)) = fun b => Q 0+∫ r in (0:ℝ)..b, G r := by
    funext b
    exact eq_add_of_sub_eq' (hprimitive b)
  rw [show (classicalShift T f : ℝ → C(AddCircle T,ℂ)) = Q from rfl,heq]
  exact (intervalIntegral.integral_hasDerivAt_right (G.continuous.intervalIntegrable 0 a)
    G.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    G.continuous.continuousAt).const_add (Q 0)

private theorem classical_shift_smooth (f : ℕ → C(AddCircle T,ℂ))
    (hf : ∀ j, HasCircleDeriv T (f j) (f (j+1))) :
    ∀ j, ContDiff ℝ ∞ (classicalShift T (f j)) := by
  have hfinite : ∀ n : ℕ, ∀ j, ContDiff ℝ (n : WithTop ℕ∞) (classicalShift T (f j)) := by
    intro n
    induction n with
    | zero => intro j; exact contDiff_zero.mpr (classicalShift T (f j)).continuous
    | succ n ih =>
      intro j
      have hd (a : ℝ) := classical_shift_hasDerivAt T (f j) (f (j+1)) (hf j) a
      have heq : deriv (classicalShift T (f j)) = classicalShift T (f (j+1)) :=
        funext fun a => (hd a).deriv
      apply (contDiff_succ_iff_deriv (n := (n : WithTop ℕ∞))).mpr
      refine ⟨fun a => (hd a).differentiableAt,by simp,?_⟩
      rw [heq]
      exact ih (j+1)
  intro j
  exact contDiff_infty.mpr (fun n => hfinite n j)

private theorem continuous_l2_shift (a : ℝ) (f : C(AddCircle T,ℂ)) :
    circleContinuousL2 T (classicalShift T f a) =
      circleL2Translation T (a:AddCircle T) (circleContinuousL2 T f) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle
    (𝕜 := ℂ) (classicalShift T f a),circle_l2_translation_ae T (a:AddCircle T)
      (circleContinuousL2 T f),
    (measurePreserving_add_right AddCircle.haarAddCircle (a:AddCircle T)).quasiMeasurePreserving.ae
      (ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) f)]
    with x hx ht hf
  exact hx.trans (hf.symm.trans ht.symm)

/-- If the initial value is represented by a full classical periodic
derivative sequence, its translation orbit is C∞ in every Sobolev norm.
The theorem places no smallness condition on its higher derivatives. -/
theorem circle_sobolev_translation_smooth_of_classical_jet (m : ℕ)
    (u : CircleSobolevSpace T m) (f : ℕ → C(AddCircle T,ℂ))
    (hf : ∀ j, HasCircleDeriv T (f j) (f (j+1)))
    (hvalue : circleSobolevCoordinate T m 0 u = circleContinuousL2 T (f 0)) :
    ContDiff ℝ ∞ (fun a : ℝ => circleSobolevTranslation T m (a:AddCircle T) u) := by
  have hcoord (j : Fin (m+1)) :
      circleSobolevCoordinate T m j u = circleContinuousL2 T (f j.val) := by
    induction j using Fin.induction with
    | zero => exact hvalue
    | succ j hj =>
      apply weak_circle_deriv_unique T (circleSobolevCoordinate T m j.castSucc u)
        (circleSobolevCoordinate T m j.succ u) (circleContinuousL2 T (f (j.val+1)))
        (circle_sobolev_weak_deriv T m u j)
      simpa only [hj] using! circle_classical_weak_deriv T (f j.val) (f (j.val+1)) (hf j.val)
  let A := PiLp 2 (fun _ : Fin (m+1) => CircleL2 T)
  let J : ℝ → A := fun a => WithLp.toLp 2
    (fun j : Fin (m+1) => circleContinuousL2 T (classicalShift T (f j.val) a))
  have hJ : ContDiff ℝ ∞ J := by
    apply (contDiff_piLp (p := (2:ENNReal))).mpr
    intro j
    exact ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).restrictScalars ℝ).contDiff.comp
      (classical_shift_smooth T f hf j.val)
  let P := (circleSobolevJetSubmodule T m).orthogonalProjectionOnto
  have heq : (fun a : ℝ => circleSobolevTranslation T m (a:AddCircle T) u) =
      fun a => P (J a) := by
    funext a
    have hjet : J a = (circleSobolevTranslation T m (a:AddCircle T) u : A) := by
      apply PiLp.ext
      intro j
      exact (continuous_l2_shift T a (f j.val)).trans
        (congrArg (circleL2Translation T (a:AddCircle T)) (hcoord j).symm)
    rw [hjet]
    exact ((circleSobolevJetSubmodule T m).orthogonalProjectionOnto_mem_subspace_eq_self _).symm
  rw [heq]
  exact (P.restrictScalars ℝ).contDiff.comp hJ

end Lemniscate
