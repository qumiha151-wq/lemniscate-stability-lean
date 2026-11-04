import Lemniscate.PeriodicClassicalFourier
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Abel

/-! Smooth profile shifts in the norm of the continuous coefficient algebra.
Point evaluation and the Bochner fundamental theorem of calculus first give
actual Banach-space derivatives. The profile ODE then bootstraps all finite
orders, without higher-derivative polynomial formulas or Fourier estimates. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ContDiff

variable (T : ℝ) [Fact (0 < T)]

/-- The shift x ↦ x+a*t, with its full continuous coefficient-algebra value. -/
def circleProfileTimeShift (q : C(AddCircle T, ℂ)) :
    C(ℝ, C(unitInterval × AddCircle T, ℂ)) :=
  ContinuousMap.curry
    ⟨fun z : ℝ × (unitInterval × AddCircle T) =>
      q (z.2.2+((z.1*(z.2.1:ℝ):ℝ):AddCircle T)),by
      apply q.continuous.comp
      exact continuous_snd.snd.add ((AddCircle.continuous_mk' T).comp
        (continuous_fst.mul (continuous_subtype_val.comp continuous_snd.fst)))⟩

private def profileShiftTime : C(unitInterval × AddCircle T, ℂ) :=
  ⟨fun z => ((z.1:ℝ):ℂ),Complex.continuous_ofReal.comp
    (continuous_subtype_val.comp continuous_fst)⟩

private theorem circle_profile_time_shift_point_deriv
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (a : ℝ) (z : unitInterval × AddCircle T) :
    HasDerivAt (fun b : ℝ => circleProfileTimeShift T q b z)
      ((profileShiftTime T*circleProfileTimeShift T p a) z) a := by
  rcases z with ⟨t,x⟩
  induction x using QuotientAddGroup.induction_on
  rename_i x
  have hparam : HasDerivAt (fun b : ℝ => x+b*(t:ℝ)) (t:ℝ) a := by
    simpa only [id_eq,one_mul] using
      (((hasDerivAt_id a).mul_const (t:ℝ)).const_add x)
  have h := (hq (x+a*(t:ℝ))).scomp a hparam
  change HasDerivAt
    (fun b : ℝ => q ((x:AddCircle T)+((b*(t:ℝ):ℝ):AddCircle T)))
    (((t:ℝ):ℂ)*p ((x:AddCircle T)+((a*(t:ℝ):ℝ):AddCircle T))) a
  simpa only [Function.comp_def,AddCircle.coe_add,real_smul,mul_comm] using! h

private theorem circle_profile_time_shift_hasDerivAt
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p) (a : ℝ) :
    HasDerivAt (circleProfileTimeShift T q)
      (profileShiftTime T*circleProfileTimeShift T p a) a := by
  let Q := circleProfileTimeShift T q
  let G : ℝ → C(unitInterval × AddCircle T, ℂ) :=
    fun b => profileShiftTime T*circleProfileTimeShift T p b
  have hG : Continuous G := continuous_const.mul (circleProfileTimeShift T p).continuous
  have hprimitive (b : ℝ) : Q b-Q 0 = ∫ r in (0:ℝ)..b, G r := by
    apply ContinuousMap.ext
    intro z
    have heval : (∫ r in (0:ℝ)..b, G r) z = ∫ r in (0:ℝ)..b, G r z :=
      ((ContinuousMap.evalCLM ℂ z).intervalIntegral_comp_comm
        (hG.intervalIntegrable 0 b)).symm
    change Q b z-Q 0 z = (∫ r in (0:ℝ)..b, G r) z
    rw [heval]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => circle_profile_time_shift_point_deriv T q p hq r z)
      (((ContinuousMap.evalCLM ℂ z).continuous.comp hG).intervalIntegrable 0 b)).symm
  have heq : (Q : ℝ → C(unitInterval × AddCircle T, ℂ)) =
      fun b => Q 0+∫ r in (0:ℝ)..b, G r := by
    funext b
    calc
      Q b = (Q b-Q 0)+Q 0 := (sub_add_cancel _ _).symm
      _ = Q 0+∫ r in (0:ℝ)..b, G r := by rw [hprimitive]; abel
  have hI : HasDerivAt (fun b : ℝ => ∫ r in (0:ℝ)..b, G r) (G a) a :=
    intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 a)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
  change HasDerivAt Q (G a) a
  rw [heq]
  exact hI.const_add (Q 0)

private theorem profile_polynomial_ode_smooth
    {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    (J : R) (Q P : ℝ → R)
    (hQ : ∀ a, HasDerivAt Q (J*P a) a)
    (hP : ∀ a, HasDerivAt P (-J*(Q a)^3) a) :
    ContDiff ℝ ∞ (fun a => (Q a,P a)) := by
  let W : ℝ → R × R := fun a => (Q a,P a)
  have hW (a : ℝ) : HasDerivAt W (J*P a,-J*(Q a)^3) a :=
    (hQ a).prodMk (hP a)
  have hdiff : Differentiable ℝ W := fun a => (hW a).differentiableAt
  have hderiv : deriv W = fun a => (J*P a,-J*(Q a)^3) :=
    funext fun a => (hW a).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ n ih =>
      have hQn : ContDiff ℝ (n : ℕ∞ω) Q := ih.fst
      have hPn : ContDiff ℝ (n : ℕ∞ω) P := ih.snd
      have hd : ContDiff ℝ (n : ℕ∞ω) (deriv W) := by
        rw [hderiv]
        fun_prop
      have hs := (contDiff_succ_iff_deriv (n := (n : ℕ∞ω))).mpr
        ⟨hdiff,by simp,hd⟩
      simpa only [Nat.cast_add,Nat.cast_one] using hs

/-- The actual profile ODE makes simultaneous time-dependent translations
smooth in the full continuous-function norm on time times the circle. -/
theorem circle_profile_time_shift_smooth
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    ContDiff ℝ ∞ (fun a : ℝ =>
      (circleProfileTimeShift T q a,circleProfileTimeShift T p a)) := by
  have hQ (a : ℝ) := circle_profile_time_shift_hasDerivAt T q p hq a
  have hP (a : ℝ) : HasDerivAt (circleProfileTimeShift T p)
      (-(profileShiftTime T)*(circleProfileTimeShift T q a)^3) a := by
    have h := circle_profile_time_shift_hasDerivAt T p (-(q^3)) hp a
    have hs : circleProfileTimeShift T (-(q^3)) a = -(circleProfileTimeShift T q a)^3 := by
      apply ContinuousMap.ext
      intro z
      rfl
    rw [hs] at h
    apply h.congr_deriv
    apply ContinuousMap.ext
    intro z
    simp only [ContinuousMap.mul_apply,ContinuousMap.neg_apply,ContinuousMap.pow_apply]
    ring
  exact profile_polynomial_ode_smooth (profileShiftTime T)
    (circleProfileTimeShift T q) (circleProfileTimeShift T p) hQ hP

end Lemniscate
