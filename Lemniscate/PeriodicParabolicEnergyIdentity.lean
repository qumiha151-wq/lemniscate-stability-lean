import Lemniscate.PeriodicFiniteParabolicSolution
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! The L2 energy identity for the actual closed parabolic space.

The proof uses the recorded Bochner primitive, rather than assuming any
pointwise time derivative.  Lebesgue differentiation supplies its derivative
almost everywhere.  Absolute continuity of its norm is controlled by the
scalar primitive of the norm of the velocity.


-/

noncomputable section
namespace Lemniscate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

private theorem primitive_norm_sq_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (w : ℝ → E) (τ : ℝ) (c : E) (t : ℝ)
    (hw : IntervalIntegrable w volume 0 t) :
    ‖c + τ • (∫ r in (0:ℝ)..t, w r)‖ ^ 2 - ‖c‖ ^ 2 =
      (2 * τ) * ∫ r in (0:ℝ)..t,
        inner ℝ (c + τ • (∫ s in (0:ℝ)..r, w s)) (w r) := by
  let P : ℝ → E := fun r => c + τ • (∫ s in (0:ℝ)..r, w s)
  let Q : ℝ → ℝ := fun r => ∫ s in (0:ℝ)..r, ‖w s‖
  have hQ : AbsolutelyContinuousOnInterval Q 0 t :=
    hw.norm.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hint (r : ℝ) (hr : r ∈ uIcc (0:ℝ) t) :
      IntervalIntegrable w volume 0 r :=
    hw.mono_set (uIcc_subset_uIcc (by simp) hr)
  have hdom (a b : ℝ) (ha : a ∈ uIcc (0:ℝ) t) (hb : b ∈ uIcc (0:ℝ) t) :
      dist ‖P a‖ ‖P b‖ ≤ |τ| * dist (Q a) (Q b) := by
    have hP : P a - P b = τ • (∫ r in b..a, w r) := by
      simp only [P, add_sub_add_left_eq_sub, ← smul_sub,
        intervalIntegral.integral_interval_sub_left (hint a ha) (hint b hb)]
    have hQsub : Q a - Q b = ∫ r in b..a, ‖w r‖ :=
      intervalIntegral.integral_interval_sub_left (hint a ha).norm (hint b hb).norm
    calc
      dist ‖P a‖ ‖P b‖ ≤ ‖P a - P b‖ := dist_norm_norm_le _ _
      _ = |τ| * ‖∫ r in b..a, w r‖ := by rw [hP, norm_smul, Real.norm_eq_abs]
      _ ≤ |τ| * |∫ r in b..a, ‖w r‖| :=
        mul_le_mul_of_nonneg_left intervalIntegral.norm_integral_le_abs_integral_norm
          (abs_nonneg τ)
      _ = |τ| * dist (Q a) (Q b) := by rw [Real.dist_eq, hQsub]
  have hnorm : AbsolutelyContinuousOnInterval (fun r => ‖P r‖) 0 t := by
    unfold AbsolutelyContinuousOnInterval at hQ ⊢
    refine squeeze_zero' (Eventually.of_forall (fun _ =>
      Finset.sum_nonneg (fun _ _ => dist_nonneg))) ?_
      (by simpa using hQ.const_mul |τ|)
    rw [eventually_inf_principal]
    filter_upwards with J hJ
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hJi := (show J ∈ AbsolutelyContinuousOnInterval.disjWithin 0 t from hJ)
    simp only [AbsolutelyContinuousOnInterval.disjWithin, mem_ofPred_eq] at hJi
    exact hdom _ _ (hJi.1 i hi).1 (hJi.1 i hi).2
  have henergy : AbsolutelyContinuousOnInterval (fun r => ‖P r‖ ^ 2) 0 t := by
    simpa only [pow_two] using hnorm.fun_mul hnorm
  calc
    ‖c + τ • (∫ r in (0:ℝ)..t, w r)‖ ^ 2 - ‖c‖ ^ 2 =
        ∫ r in (0:ℝ)..t, deriv (fun s => ‖P s‖ ^ 2) r := by
      simpa only [P, intervalIntegral.integral_same, smul_zero, add_zero] using
        henergy.integral_deriv_eq_sub.symm
    _ = ∫ r in (0:ℝ)..t, (2 * τ) * inner ℝ (P r) (w r) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hw.ae_hasDerivAt_integral] with r hr hrt
      have hd : HasDerivAt P (τ • w r) r :=
        ((hr (uIoc_subset_uIcc hrt) 0 (by simp)).const_smul τ).const_add c
      rw [hd.norm_sq.deriv, real_inner_smul_right]
      ring
    _ = (2 * τ) * ∫ r in (0:ℝ)..t, inner ℝ (P r) (w r) :=
      intervalIntegral.integral_const_mul _ _

/-- The quadratic energy formula for an actual Bochner primitive on the
unit interval. No pointwise differentiability of the curve is assumed. -/
theorem unit_interval_primitive_norm_sq_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (τ : ℝ) (q v : unitInterval → E)
    (hv : Integrable v (volume : Measure unitInterval))
    (hprimitive : ∀ r : unitInterval,
      q r-q 0 = τ • (∫ s in Iic r, v s ∂volume)) (t : unitInterval) :
    ‖q t‖ ^ 2-‖q 0‖ ^ 2 =
      (2*τ) * ∫ r in Iic t, (inner ℂ (q r) (v r)).re ∂volume := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp (r : unitInterval) : clamp (r:ℝ) = r := Set.projIcc_val zero_le_one r
  let w : ℝ → E := fun r => v (clamp r)
  have hwOn : IntegrableOn w (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def, w, hclamp] using hv
  have hw01 : IntervalIntegrable w volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hwOn
  have hw : IntervalIntegrable w volume 0 (t:ℝ) :=
    hw01.mono_set (by
      rw [uIcc_of_le t.property.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl t.property.2)
  let P : ℝ → E := fun r => q 0 + τ • (∫ s in (0:ℝ)..r, w s)
  have hP (r : unitInterval) : q r = P (r:ℝ) := by
    have hprim : q r-q 0 = τ • (∫ s in (0:ℝ)..(r:ℝ), w s) := by
      rw [← unit_interval_setIntegral w r]
      simpa only [w,hclamp] using hprimitive r
    dsimp only [P]
    rw [← hprim]
    abel
  have henergy := primitive_norm_sq_energy w τ (q 0) (t:ℝ) hw
  change ‖P (t:ℝ)‖ ^ 2-‖q 0‖ ^ 2 =
    (2*τ) * ∫ r in (0:ℝ)..(t:ℝ), inner ℝ (P r) (w r) at henergy
  rw [hP t]
  refine henergy.trans ?_
  rw [← unit_interval_setIntegral (fun r => inner ℝ (P r) (w r)) t]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro r _
  change inner ℝ (P (r:ℝ)) (w (r:ℝ)) = (inner ℂ (q r) (v r)).re
  rw [← hP r]
  simpa only [w,hclamp,RCLike.re_eq_complex_re] using (real_inner_eq_re_inner ℂ (q r) (v r))

end Lemniscate
