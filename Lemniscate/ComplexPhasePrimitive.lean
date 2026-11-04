import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! The integrating-factor identity for an actual complex L1 primitive.
Lebesgue differentiation and absolute continuity provide the derivatives;
no classical time derivative of the forcing is assumed.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set Filter
open scoped Topology

private theorem complex_primitive_absolutely_continuous
    (f : ℝ → ℂ) (hf : IntervalIntegrable f volume (0:ℝ) 1) :
    AbsolutelyContinuousOnInterval (fun r => ∫ s in (0:ℝ)..r, f s) 0 1 := by
  let P : ℝ → ℂ := fun r => ∫ s in (0:ℝ)..r, f s
  let Q : ℝ → ℝ := fun r => ∫ s in (0:ℝ)..r, ‖f s‖
  have hQ : AbsolutelyContinuousOnInterval Q 0 1 :=
    hf.norm.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hint (r : ℝ) (hr : r ∈ uIcc (0:ℝ) 1) :
      IntervalIntegrable f volume 0 r :=
    hf.mono_set (uIcc_subset_uIcc (by simp) hr)
  have hdist (a b : ℝ) (ha : a ∈ uIcc (0:ℝ) 1) (hb : b ∈ uIcc (0:ℝ) 1) :
      dist (P a) (P b) ≤ dist (Q a) (Q b) := by
    have hP : P a-P b = ∫ r in b..a, f r :=
      intervalIntegral.integral_interval_sub_left (hint a ha) (hint b hb)
    have hQsub : Q a-Q b = ∫ r in b..a, ‖f r‖ :=
      intervalIntegral.integral_interval_sub_left (hint a ha).norm (hint b hb).norm
    calc
      _ = ‖∫ r in b..a, f r‖ := by rw [dist_eq_norm,hP]
      _ ≤ |∫ r in b..a, ‖f r‖| := intervalIntegral.norm_integral_le_abs_integral_norm
      _ = _ := by rw [Real.dist_eq,hQsub]
  unfold AbsolutelyContinuousOnInterval at hQ ⊢
  refine squeeze_zero' (Eventually.of_forall (fun _ =>
    Finset.sum_nonneg (fun _ _ => dist_nonneg))) ?_ (by simpa only [Q] using hQ)
  rw [eventually_inf_principal]
  filter_upwards with J hJ
  apply Finset.sum_le_sum
  intro i hi
  have hJi := (show J ∈ AbsolutelyContinuousOnInterval.disjWithin 0 1 from hJ)
  simp only [AbsolutelyContinuousOnInterval.disjWithin,mem_ofPred_eq] at hJi
  exact hdist _ _ (hJi.1 i hi).1 (hJi.1 i hi).2

/-- Multiplication of a genuine complex L1 primitive by exp(z*t) obeys
the integral product rule at every time in the unit interval. -/
theorem complex_phase_primitive
    (f : ℝ → ℂ) (hf : IntervalIntegrable f volume (0:ℝ) 1)
    (y0 z : ℂ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    let y : ℝ → ℂ := fun r => y0+∫ s in (0:ℝ)..r, f s
    Complex.exp (z*(t:ℂ))*y t-y0 =
      ∫ s in (0:ℝ)..t,
        (Complex.exp (z*(s:ℂ))*f s+z*Complex.exp (z*(s:ℂ))*y s) := by
  dsimp only
  let y : ℝ → ℂ := fun r => y0+∫ s in (0:ℝ)..r, f s
  let φ : ℝ → ℂ := fun r => Complex.exp (z*(r:ℂ))
  let g : ℝ → ℂ := fun r => φ r*f r+z*φ r*y r
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ => y0) 0 1 :=
    (show ContDiffOn ℝ 1 (fun _ : ℝ => y0) (uIcc 0 1) from
      contDiff_const.contDiffOn).absolutelyContinuousOnInterval
  have hyac : AbsolutelyContinuousOnInterval y 0 1 :=
    hconstant.fun_add (complex_primitive_absolutely_continuous f hf)
  have hφsmooth : ContDiff ℝ 1 φ :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hφac : AbsolutelyContinuousOnInterval φ 0 1 :=
    hφsmooth.contDiffOn.absolutelyContinuousOnInterval
  have hφderiv (r : ℝ) : HasDerivAt φ (z*φ r) r := by
    have hR : HasDerivAt (fun s : ℝ => (s:ℂ)) (1:ℂ) r :=
      by simpa only using! Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    exact (hR.const_mul z).cexp.congr_deriv (by dsimp only [φ]; simp only [mul_one]; ring)
  have hg : IntervalIntegrable g volume (0:ℝ) 1 :=
    (hf.continuousOn_mul hφsmooth.continuous.continuousOn).add
      ((continuousOn_const.mul hφsmooth.continuous.continuousOn).mul
        hyac.continuousOn).intervalIntegrable
  let W : ℝ → ℂ := fun r => φ r*y r-∫ s in (0:ℝ)..r, g s
  have hWac : AbsolutelyContinuousOnInterval W 0 1 := by
    have hp : AbsolutelyContinuousOnInterval (fun r => φ r*y r) 0 1 := by
      simpa only [smul_eq_mul] using! hφac.fun_smul hyac
    exact hp.fun_sub (complex_primitive_absolutely_continuous g hg)
  have hWd : ∀ᵐ r ∂volume,
      r ∈ uIcc (0:ℝ) 1 → HasDerivAt W 0 r := by
    filter_upwards [hf.ae_hasDerivAt_integral,hg.ae_hasDerivAt_integral]
      with r hfr hgr hr
    have hyr : HasDerivAt y (f r) r := (hfr hr 0 (by simp)).const_add y0
    apply ((hφderiv r).mul hyr |>.sub (hgr hr 0 (by simp))).congr_deriv
    dsimp only [g]
    ring
  obtain ⟨C,hC⟩ := hWac.const_of_ae_hasDerivAt_zero hWd
  have hWzero : W 0 = y0 := by simp [W,φ,y]
  have hWt : W t = y0 :=
    (hC t (by simpa only [uIcc_of_le zero_le_one] using ht)).trans
      ((hC 0 (by simp)).symm.trans hWzero)
  change φ t*y t-(∫ s in (0:ℝ)..t, g s) = y0 at hWt
  change φ t*y t-y0 = ∫ s in (0:ℝ)..t, g s
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hWt).trans (add_comm _ _))

end Lemniscate
