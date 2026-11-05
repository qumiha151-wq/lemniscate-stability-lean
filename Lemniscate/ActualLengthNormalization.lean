import Lemniscate.NormalGraphCjEstimate
import Lemniscate.OrderIsoDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Real.Pointwise

/-! Actual-length normalization of a periodic geometric convergence result.
The same parameter changes and the same limiting rotation are retained. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

def periodicCurveLength (P : ℝ) (γ : ℝ → ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..P, ‖deriv γ s‖

private theorem finite_order_le_infty (n : ℕ) : (n : ℕ∞ω) ≤ ∞ :=
  (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)).le

private theorem derivative_sup_bounded (Q : ℝ) (hQ : 0 < Q) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Q) (n : ℕ) :
    BddAbove (range (fun x : ℝ => ‖iteratedDeriv n f x‖)) := by
  have hn : ContDiff ℝ (n : ℕ∞ω) f := hf.of_le (finite_order_le_infty n)
  have hcont := (hn.continuous_iteratedDeriv n le_rfl).norm
  have hper : Function.Periodic (fun x => ‖iteratedDeriv n f x‖) Q := by
    intro x
    exact congrArg norm (periodic_iterated_deriv Q f hp n x)
  exact (hper.compact_of_continuous hQ.ne' hcont).bddAbove

private theorem periodic_cj_nonneg (j : ℕ) (f : ℝ → ℂ) : 0 ≤ periodicCjNorm j f := by
  apply Finset.sum_nonneg
  intro i _
  apply Real.sSup_nonneg
  rintro _ ⟨x, rfl⟩
  exact norm_nonneg _

private theorem derivative_le_periodic_cj_one (Q : ℝ) (hQ : 0 < Q) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f Q) (x : ℝ) :
    ‖deriv f x‖ ≤ periodicCjNorm 1 f := by
  have hs : ‖iteratedDeriv 1 f x‖ ≤
      sSup (range (fun y : ℝ => ‖iteratedDeriv 1 f y‖)) :=
    le_csSup (derivative_sup_bounded Q hQ f hf hp 1) (mem_range_self x)
  have hh : sSup (range (fun y : ℝ => ‖iteratedDeriv 1 f y‖)) ≤ periodicCjNorm 1 f := by
    apply Finset.single_le_sum (f := fun i : Fin 2 =>
      sSup (range (fun y : ℝ => ‖iteratedDeriv i.val f y‖)))
      (fun i _ => ?_) (Finset.mem_univ (1 : Fin 2))
    apply Real.sSup_nonneg
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _
  simpa only [iteratedDeriv_one] using hs.trans hh

private theorem periodic_cj_linear_combination (Q : ℝ) (hQ : 0 < Q)
    (j : ℕ) (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f Q) (hgp : Function.Periodic g Q) (a b : ℂ) :
    periodicCjNorm j (fun x => a * f x + b * g x) ≤
      ‖a‖ * periodicCjNorm j f + ‖b‖ * periodicCjNorm j g := by
  unfold periodicCjNorm
  calc
    _ ≤ ∑ i : Fin (j + 1),
        (‖a‖ * sSup (range (fun x : ℝ => ‖iteratedDeriv i.val f x‖)) +
          ‖b‖ * sSup (range (fun x : ℝ => ‖iteratedDeriv i.val g x‖))) := by
      apply Finset.sum_le_sum
      intro i _
      apply csSup_le (range_nonempty _)
      rintro _ ⟨x, rfl⟩
      have hfi : ContDiffAt ℝ (i.val : ℕ∞ω) f x :=
        (hf.of_le (finite_order_le_infty i.val)).contDiffAt
      have hgi : ContDiffAt ℝ (i.val : ℕ∞ω) g x :=
        (hg.of_le (finite_order_le_infty i.val)).contDiffAt
      change ‖iteratedDeriv i.val (fun y => a * f y + b * g y) x‖ ≤ _
      have haf : ContDiffAt ℝ (i.val : ℕ∞ω) (fun y => a * f y) x := contDiffAt_const.mul hfi
      have hbg : ContDiffAt ℝ (i.val : ℕ∞ω) (fun y => b * g y) x := contDiffAt_const.mul hgi
      rw [iteratedDeriv_fun_add haf hbg, iteratedDeriv_const_mul_field a f,
        iteratedDeriv_const_mul_field b g]
      have hfx := le_csSup (derivative_sup_bounded Q hQ f hf hfp i.val) (mem_range_self x)
      have hgx := le_csSup (derivative_sup_bounded Q hQ g hg hgp i.val) (mem_range_self x)
      exact (norm_add_le _ _).trans (by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hfx (norm_nonneg a))
          (mul_le_mul_of_nonneg_left hgx (norm_nonneg b)))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Length is invariant under the actual smooth increasing circle lift,
including an arbitrary starting arclength phase. -/
theorem periodic_curve_length_reparametrize
    (P Q : ℝ) (γ : ℝ → ℂ) (χ : ℝ ≃o ℝ)
    (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P)
    (hχ : ContDiff ℝ ∞ (χ : ℝ → ℝ))
    (hχinv : ContDiff ℝ ∞ (χ.symm : ℝ → ℝ))
    (hdeck : ∀ s, χ (s + Q) = χ s + P) :
    periodicCurveLength Q (fun s => γ (χ s)) = periodicCurveLength P γ := by
  have hγdiff := (contDiff_infty_iff_deriv.mp hγ).1
  have hχdiff := (contDiff_infty_iff_deriv.mp hχ).1
  have hχinvDiff := (contDiff_infty_iff_deriv.mp hχinv).1
  have hγcont := (contDiff_infty_iff_deriv.mp hγ).2.continuous
  have hχcont := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hspeed (s : ℝ) : ‖deriv (fun x => γ (χ x)) s‖ =
      ‖deriv γ (χ s)‖ * deriv (χ : ℝ → ℝ) s := by
    have hd := (hγdiff (χ s)).hasDerivAt.scomp s (hχdiff s).hasDerivAt
    change ‖deriv (γ ∘ (χ : ℝ → ℝ)) s‖ = _
    rw [hd.deriv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (order_iso_deriv_pos χ hχdiff hχinvDiff s)]
    ring
  have hperiod : Function.Periodic (fun s => ‖deriv γ s‖) P := by
    intro s
    exact congrArg norm (by
      simpa only [iteratedDeriv_one] using periodic_iterated_deriv P γ hp 1 s)
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := 0) (b := Q) (f := (χ : ℝ → ℝ)) (f' := deriv (χ : ℝ → ℝ))
    (g := fun s => ‖deriv γ s‖) (fun s _ => (hχdiff s).hasDerivAt)
    hχcont.continuousOn hγcont.norm
  dsimp only [Function.comp_def] at hsubst
  unfold periodicCurveLength
  simp_rw [hspeed]
  rw [hsubst, show χ Q = χ 0 + P by simpa only [zero_add] using hdeck 0]
  simpa only [zero_add] using hperiod.intervalIntegral_add_eq (χ 0) 0

private theorem periodic_curve_length_div (P : ℝ) (γ : ℝ → ℂ) (c : ℝ) (hc : 0 < c) :
    periodicCurveLength P (fun s => γ s / (c : ℂ)) = periodicCurveLength P γ / c := by
  unfold periodicCurveLength
  simp_rw [deriv_div_const, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const]

private theorem periodic_curve_length_difference (Q : ℝ) (hQ : 0 < Q)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f Q) (hgp : Function.Periodic g Q) :
    |periodicCurveLength Q f - periodicCurveLength Q g| ≤
      periodicCjNorm 1 (fun x => f x - g x) * Q := by
  have hfd := (contDiff_infty_iff_deriv.mp hf).1
  have hgd := (contDiff_infty_iff_deriv.mp hg).1
  have hfc := (contDiff_infty_iff_deriv.mp hf).2.continuous.norm
  have hgc := (contDiff_infty_iff_deriv.mp hg).2.continuous.norm
  have hp : Function.Periodic (fun x => f x - g x) Q := fun x => by
    change f (x + Q) - g (x + Q) = f x - g x
    rw [hfp x, hgp x]
  have hb (x : ℝ) : ‖‖deriv f x‖ - ‖deriv g x‖‖ ≤
      periodicCjNorm 1 (fun x => f x - g x) := by
    calc
      _ ≤ ‖deriv f x - deriv g x‖ := by
        simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (deriv f x) (deriv g x)
      _ = ‖deriv (fun y => f y - g y) x‖ := by rw [deriv_fun_sub (hfd x) (hgd x)]
      _ ≤ _ := derivative_le_periodic_cj_one Q hQ _ (hf.sub hg) hp x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := Q)
    (fun x _ => hb x)
  rw [intervalIntegral.integral_sub (hfc.intervalIntegrable 0 Q)
    (hgc.intervalIntegrable 0 Q)] at hi
  simpa only [periodicCurveLength, Real.norm_eq_abs, sub_zero, abs_of_pos hQ] using hi

/-- Smooth convergence after division by an expanding scale implies smooth
convergence after division by the actual length.  The reference is unit speed;
the parameter changes and rotation are precisely the input ones. -/
theorem periodic_actual_length_normalization
    (P Q : ℝ) (hQ : 0 < Q) (β : ℝ → ℂ)
    (hβ : ContDiff ℝ ∞ β) (hβper : Function.Periodic β Q)
    (hβunit : ∀ s, ‖deriv β s‖ = 1)
    (R : ℂ) (hR : ‖R‖ = 1) (Y : ℝ → ℝ → ℂ)
    (hY : ∀ t, 0 ≤ t → ContDiff ℝ ∞ (Y t) ∧ Function.Periodic (Y t) P)
    (χ : ℝ → (ℝ ≃o ℝ))
    (hχ : ∀ t, 0 ≤ t → ContDiff ℝ ∞ (χ t : ℝ → ℝ) ∧
      ContDiff ℝ ∞ ((χ t).symm : ℝ → ℝ) ∧ ∀ s, χ t (s + Q) = χ t s + P)
    (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t)
    (hconv : ∀ j : ℕ, Tendsto (fun t => periodicCjNorm j
      (fun s => Y t (χ t s) / (ρ t : ℂ) - R * β s)) atTop (𝓝 0)) :
    Tendsto (fun t => periodicCurveLength P (Y t) / ρ t) atTop (𝓝 Q) ∧
    ∀ j : ℕ, Tendsto (fun t => periodicCjNorm j
      (fun s => Y t (χ t s) / (periodicCurveLength P (Y t) : ℂ) -
        R * β s / (Q : ℂ))) atTop (𝓝 0) := by
  let L : ℝ → ℝ := fun t => periodicCurveLength P (Y t)
  let Z : ℝ → ℝ → ℂ := fun t s => Y t (χ t s) / (ρ t : ℂ)
  let g : ℝ → ℂ := fun s => R * β s
  let E : ℝ → ℝ → ℂ := fun t s => Z t s - g s
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul hβ
  have hgp : Function.Periodic g Q := fun s => by dsimp only [g]; rw [hβper s]
  have hgunit (s : ℝ) : ‖deriv g s‖ = 1 := by
    have hd := ((contDiff_infty_iff_deriv.mp hβ).1 s).hasDerivAt.const_mul R
    rw [hd.deriv, norm_mul, hR, hβunit s, mul_one]
  have hglength : periodicCurveLength Q g = Q := by
    simp only [periodicCurveLength, hgunit, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, mul_one]
  have hZ (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (Z t) ∧ Function.Periodic (Z t) Q := by
    constructor
    · have hc : ContDiff ℝ ∞ (fun s => Y t (χ t s)) := (hY t ht).1.comp (hχ t ht).1
      simpa only [Z, div_eq_mul_inv] using ContDiff.mul hc
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (ρ t : ℂ)⁻¹))
    · intro s
      dsimp only [Z]
      rw [(hχ t ht).2.2 s, (hY t ht).2 (χ t s)]
  have hZlength (t : ℝ) (ht : 0 ≤ t) : periodicCurveLength Q (Z t) = L t / ρ t := by
    rw [show Z t = fun s => (fun x => Y t (χ t x)) s / (ρ t : ℂ) from rfl,
      periodic_curve_length_div Q _ _ (hρ t ht),
      periodic_curve_length_reparametrize P Q (Y t) (χ t)
        (hY t ht).1 (hY t ht).2 (hχ t ht).1 (hχ t ht).2.1 (hχ t ht).2.2]
  have hratio : Tendsto (fun t => L t / ρ t) atTop (𝓝 Q) := by
    have hb : ∀ᶠ t in atTop, ‖L t / ρ t - Q‖ ≤ periodicCjNorm 1 (E t) * Q := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have hh := periodic_curve_length_difference Q hQ (Z t) g
        (hZ t ht).1 hg (hZ t ht).2 hgp
      simpa only [E, hZlength t ht, hglength, Real.norm_eq_abs] using hh
    have hz : Tendsto (fun t => L t / ρ t - Q) atTop (𝓝 0) :=
      squeeze_zero_norm' hb (by simpa only [zero_mul] using (hconv 1).mul_const Q)
    simpa only [sub_add_cancel, zero_add] using hz.add_const Q
  refine ⟨hratio, ?_⟩
  let c : ℝ → ℝ := fun t => (L t / ρ t)⁻¹
  have hc : Tendsto c atTop (𝓝 Q⁻¹) := hratio.inv₀ hQ.ne'
  have hd : Tendsto (fun t => |c t - Q⁻¹|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hc.sub_const Q⁻¹).abs
  have hLn : ∀ᶠ t in atTop, L t ≠ 0 := by
    filter_upwards [hratio.eventually (eventually_ne_nhds hQ.ne')] with t ht
    intro hzero
    apply ht
    rw [hzero, zero_div]
  intro j
  have hmajor : Tendsto (fun t => |c t| * periodicCjNorm j (E t) +
      |c t - Q⁻¹| * periodicCjNorm j g) atTop (𝓝 0) := by
    have h1 := hc.abs.mul (hconv j)
    have h2 := hd.mul_const (periodicCjNorm j g)
    simpa only [mul_zero, zero_mul, zero_add] using h1.add h2
  apply squeeze_zero' (Eventually.of_forall (fun t => periodic_cj_nonneg j _)) ?_ hmajor
  filter_upwards [eventually_ge_atTop (0 : ℝ), hLn] with t ht hLt
  have hEt : ContDiff ℝ ∞ (E t) := (hZ t ht).1.sub hg
  have hEp : Function.Periodic (E t) Q := fun s => by
    dsimp only [E]
    rw [(hZ t ht).2 s, hgp s]
  have hid : (fun s => Y t (χ t s) / (L t : ℂ) - R * β s / (Q : ℂ)) =
      (fun s => (c t : ℂ) * E t s + ((c t - Q⁻¹ : ℝ) : ℂ) * g s) := by
    funext s
    have hρt : (ρ t : ℂ) ≠ 0 := by exact_mod_cast (hρ t ht).ne'
    have hLtC : (L t : ℂ) ≠ 0 := by exact_mod_cast hLt
    have hQC : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
    dsimp only [c, E, Z, g]
    push_cast
    field_simp [hρt, hLtC, hQC]
    <;> ring
  rw [hid]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    periodic_cj_linear_combination Q hQ j (E t) g hEt hg hEp hgp
      (c t : ℂ) ((c t - Q⁻¹ : ℝ) : ℂ)

end Lemniscate
