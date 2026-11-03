import Lemniscate.PeriodicWeakFirst
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Algebra.Ring.Periodic

/-! A continuous periodic weak derivative is the actual classical derivative.

The proof constructs the zero-mean periodic primitive by the fundamental
theorem of calculus, and uses Fourier uniqueness only to identify the additive
constant. No classical regularity is assumed for the weakly differentiated f.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped Interval

variable (T : ℝ) [Fact (0 < T)]

theorem circle_classical_deriv_of_continuous_weak
    (f g : C(AddCircle T, ℂ))
    (hfg : HasWeakCircleDeriv T (circleContinuousL2 T f) (circleContinuousL2 T g)) :
    HasCircleDeriv T f g := by
  have hT : 0 < T := Fact.out
  have hcoeff (n : ℤ) : fourierCoeff g n = circleFrequencyFactor T n*fourierCoeff f n := by
    simpa only [circle_continuous_l2_fourier] using
      fourier_of_weak_circle_deriv T (circleContinuousL2 T f) (circleContinuousL2 T g) hfg n
  have hzero : fourierCoeff g 0 = 0 := by
    simpa [circleFrequencyFactor] using hcoeff 0
  let G : ℝ → ℂ := fun x => g (x : AddCircle T)
  have hGc : Continuous G := g.continuous.comp (AddCircle.continuous_mk' T)
  have hGperiod : Function.Periodic G T := by
    intro x
    simp only [G,AddCircle.coe_add_period]
  have hIzero : (∫ x : ℝ in (0:ℝ)..T, G x) = 0 := by
    have hz := hzero
    rw [fourierCoeff_eq_intervalIntegral g 0 0] at hz
    simp only [zero_add,neg_zero,fourier_zero,one_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left (one_div_ne_zero (ne_of_gt hT))
  let P : ℝ → ℂ := fun x => ∫ u : ℝ in (0:ℝ)..x, G u
  have hP (x : ℝ) : HasDerivAt P (G x) x :=
    intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 x)
      hGc.aestronglyMeasurable.stronglyMeasurableAtFilter hGc.continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun x => (hP x).continuousAt
  have hPperiod : Function.Periodic P T := by
    intro x
    simpa only [P,zero_add,hIzero,add_zero] using
      hGperiod.intervalIntegral_add_eq_add 0 x (fun a b => hGc.intervalIntegrable a b)
  let R : C(AddCircle T, ℂ) :=
    { toFun := hPperiod.lift
      continuous_toFun := hPc.quotient_lift _ }
  have hR : HasCircleDeriv T R g := fun x => hP x
  have hnonzero (n : ℤ) (hn : n ≠ 0) : fourierCoeff f n = fourierCoeff R n := by
    have hnr : (n:ℝ) ≠ 0 := by exact_mod_cast hn
    have hbase : (2*Real.pi/T:ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hω : circleFrequencyFactor T n ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero hbase hnr)) I_ne_zero
    apply mul_left_cancel₀ hω
    exact (hcoeff n).symm.trans (fourierCoeff_classical_deriv T R g hR n)
  let c : ℂ := fourierCoeff f 0-fourierCoeff R 0
  have heval (u : C(AddCircle T, ℂ)) (n : ℤ) :
      inner ℂ (fourierBasis (T := T) n) (circleContinuousL2 T u) = fourierCoeff u n := by
    rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr,circle_continuous_l2_fourier]
  have hL2 : circleContinuousL2 T f =
      circleContinuousL2 T R+c • fourierBasis (T := T) 0 := by
    apply (fourierBasis (T := T)).repr.injective
    ext n
    rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply,
      inner_add_right,inner_smul_right,heval f n,heval R n]
    rw [orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal n 0]
    by_cases hn : n = 0
    · subst n
      simp only [ite_true,mul_one]
      dsimp only [c]
      ring
    · simpa [hn,Ne.symm hn] using hnonzero n hn
  have hC : f = R+c • fourier (T := T) 0 := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 T f = circleContinuousL2 T (R+c • fourier (T := T) 0)
    have hmap : circleContinuousL2 T (R+c • fourier (T := T) 0) =
        circleContinuousL2 T R+c • fourierBasis (T := T) 0 := by
      change ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (R+c • fourier (T := T) 0) = _
      rw [map_add,map_smul]
      change circleContinuousL2 T R+c • circleContinuousL2 T (fourier (T := T) 0) = _
      rw [circle_continuous_l2_fourier_basis]
    rw [hmap]
    exact hL2
  have hfunction : (fun x : ℝ => f (x:AddCircle T)) =
      fun x : ℝ => R (x:AddCircle T)+c := by
    funext x
    rw [hC]
    change R (x:AddCircle T)+c*fourier 0 (x:AddCircle T) = R (x:AddCircle T)+c
    rw [fourier_zero,mul_one]
  intro x
  rw [hfunction]
  exact (hR x).add_const c

end Lemniscate
