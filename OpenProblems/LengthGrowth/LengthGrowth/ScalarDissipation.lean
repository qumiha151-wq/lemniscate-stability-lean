import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert

/-!
# Scalar dissipation consequences

This file formalizes real-variable consequences of an assumed scalar
inequality `(L')^2 <= -H'`. It does NOT formalize the geometric free elastic
flow or derive this inequality from its PDE. For the intended application,
`H = E^2` and the PDE identities must be established separately.
-/

namespace FreeElasticScalar

/-- A squared secant bound from quadratic dissipation, proved by the
mean-value monotonicity theorem (no integral assumptions are required). -/
theorem secant_sq_le_energy_drop
    (L H l h : ℝ → ℝ) (s t : ℝ) (hst : s < t)
    (hLc : ContinuousOn L (Set.Icc s t))
    (hHc : ContinuousOn H (Set.Icc s t))
    (hLd : ∀ x ∈ Set.Ioo s t, HasDerivAt L (l x) x)
    (hHd : ∀ x ∈ Set.Ioo s t, HasDerivAt H (h x) x)
    (hdiss : ∀ x ∈ Set.Ioo s t, (l x)^2 ≤ -(h x)) :
    (L t - L s)^2 ≤ (t-s) * (H s-H t) := by
  let a : ℝ := (L t-L s)/(t-s)
  let f : ℝ → ℝ := fun x => H x + (2*a)*L x - a^2*x
  have hfcont : ContinuousOn f (Set.Icc s t) := by
    exact (hHc.add (continuousOn_const.mul hLc)).sub
      (continuousOn_const.mul continuousOn_id)
  have hfd : ∀ x ∈ Set.Ioo s t,
      HasDerivAt f (h x+(2*a)*l x-a^2) x := by
    intro x hx
    convert! ((hHd x hx).add ((hLd x hx).const_mul (2*a))).sub
      ((hasDerivAt_id x).const_mul (a^2)) using 1
    ring
  have hfanti : AntitoneOn f (Set.Icc s t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) hfcont
      (f' := fun x => h x+(2*a)*l x-a^2)
    · intro x hx
      exact (hfd x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hd := hdiss x (by simpa only [interior_Icc] using hx)
      nlinarith [sq_nonneg (l x-a)]
  have hfend := hfanti (show s ∈ Set.Icc s t from ⟨le_rfl,hst.le⟩)
    (show t ∈ Set.Icc s t from ⟨hst.le,le_rfl⟩) hst.le
  have hbound : 2*a*(L t-L s)-a^2*(t-s) ≤ H s-H t := by
    dsimp [f] at hfend
    nlinarith
  have ha : a*(t-s) = L t-L s := by
    dsimp [a]
    exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hst))
  calc
    (L t-L s)^2 = (t-s)*(2*a*(L t-L s)-a^2*(t-s)) := by
      rw [← ha]
      ring
    _ ≤ (t-s)*(H s-H t) :=
      mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hst.le)

#print axioms secant_sq_le_energy_drop

/-- The algebraic step at a time when length has doubled. -/
theorem doubling_algebra (ell e K t : ℝ)
    (hell : 0 ≤ ell) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hnorm : e*ell ≤ 2*K)
    (hsec : ell^2 ≤ 4*t*e^2) :
    ell^4 ≤ 16*K^2*t := by
  have hp := mul_self_le_mul_self (mul_nonneg he hell) hnorm
  have hq := mul_le_mul_of_nonneg_right hsec (sq_nonneg ell)
  have hr := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*t by positivity)
  nlinarith

/-- A uniform bound for the scale-invariant product `E*L` and the
restart estimate imply a fourth-power length bound. The proof uses the
intermediate value theorem, and does not assume length is monotone.
All hypotheses concern scalar functions; their geometric derivation is
outside this file. -/
theorem conditional_fourth_power_bound
    (L E : ℝ → ℝ) (K t : ℝ) (ht : 0 ≤ t)
    (hLc : ContinuousOn L (Set.Icc 0 t))
    (hLpos : ∀ s ∈ Set.Icc 0 t, 0 ≤ L s)
    (hEpos : ∀ s ∈ Set.Icc 0 t, 0 ≤ E s)
    (hprod : ∀ s ∈ Set.Icc 0 t, E s*L s ≤ K)
    (hrestart : ∀ s ∈ Set.Icc 0 t,
      (L t-L s)^2 ≤ (t-s)*((E s)^2-(E t)^2)) :
    (L t)^4 ≤ max ((2*L 0)^4) (16*K^2*t) := by
  have hL0 : 0 ≤ L 0 := hLpos 0 ⟨le_rfl, ht⟩
  have hLt : 0 ≤ L t := hLpos t ⟨ht, le_rfl⟩
  by_cases hsmall : L t ≤ 2*L 0
  · have hpow : (L t)^4 ≤ (2*L 0)^4 := by
      exact pow_le_pow_left₀ hLt hsmall 4
    exact hpow.trans (le_max_left _ _)
  · have hlarge : 2*L 0 < L t := lt_of_not_ge hsmall
    obtain ⟨s, hs, hLs⟩ := intermediate_value_Icc ht hLc
      (show L t/2 ∈ Set.Icc (L 0) (L t) from ⟨by linarith, by linarith⟩)
    have hnorm : E s*L t ≤ 2*K := by
      have hp := hprod s hs
      rw [hLs] at hp
      nlinarith
    have hsec : (L t)^2 ≤ 4*t*(E s)^2 := by
      have hr := hrestart s hs
      rw [hLs] at hr
      have h1 := mul_nonneg hs.1 (sq_nonneg (E s))
      have h2 := mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg (E t))
      nlinarith
    exact (doubling_algebra (L t) (E s) K t hLt (hEpos s hs) ht hnorm hsec).trans
      (le_max_right _ _)

#print axioms conditional_fourth_power_bound

end FreeElasticScalar
