import OpenTranslators.Geometry
import OpenTranslators.DerivativeLimit
import Mathlib.Topology.Order.MonotoneConvergence

/-! Bounded-curvature rigidity for actual global translator solutions.
The first estimates derive bounded curvature derivative from the actual ODE,
and compute the actual stress. No stress identity or derivative bound is assumed. -/

namespace OpenTranslator.BoundedCurvature
noncomputable section
open Set Filter
open scoped Topology

/-- A coarse global derivative estimate from two actual derivatives and bounds.
The proof uses a unit-interval mean-value point and the derivative Lipschitz bound. -/
theorem derivative_bound_of_bounded_and_second
    {f g h : ℝ → ℝ} {K M : ℝ}
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : ∀ s, HasDerivAt g (h s) s)
    (hfb : ∀ s, |f s| ≤ K) (hhb : ∀ s, |h s| ≤ M) (s : ℝ) :
    |g s| ≤ 2*K+M := by
  have hM : 0 ≤ M := (abs_nonneg (h 0)).trans (hhb 0)
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope f g (show s < s+1 by linarith)
    ((continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).continuousOn)
    (fun x _ => hf x)
  rw [show s+1-s=1 by ring, div_one] at he
  have hgc : |g c| ≤ 2*K := by
    rw [he]
    exact (abs_sub _ _).trans (by linarith [hfb (s+1), hfb s])
  have hlip : |g s-g c| ≤ M * |s-c| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := g) (f' := h) (x := c) (y := s)
        (fun x (_ : x ∈ (univ : Set ℝ)) => (hg x).hasDerivWithinAt)
        (fun x _ => hhb x) convex_univ (mem_univ c) (mem_univ s)
  have hdist : |s-c| ≤ 1 := by
    rw [abs_of_nonpos (by linarith [hc.1])]
    linarith [hc.2]
  calc
    |g s| = |(g s-g c)+g c| := by rw [sub_add_cancel]
    _ ≤ |g s-g c|+|g c| := abs_add_le _ _
    _ ≤ 2*K+M := by nlinarith

theorem lipschitz_bound_of_derivative_bound {f g : ℝ → ℝ} {C : ℝ}
    (hd : ∀ s, HasDerivAt f (g s) s) (hb : ∀ s, |g s| ≤ C) (x y : ℝ) :
    |f x-f y| ≤ C*|x-y| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := g) (x := y) (y := x)
      (fun s (_ : s ∈ (univ : Set ℝ)) => (hd s).hasDerivWithinAt)
      (fun s _ => hb s) convex_univ (mem_univ y) (mem_univ x)

theorem tendsto_zero_of_square {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : Tendsto (fun s => f s ^ 2) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have h := (Real.continuous_sqrt.tendsto 0).comp hf
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h

theorem derivative_tendsto_zero_end {f g : ℝ → ℝ} {l : Filter ℝ} {C a : ℝ}
    (hl : l = atTop ∨ l = atBot)
    (hd : ∀ s, HasDerivAt f (g s) s) (hC : 0 ≤ C)
    (hLip : ∀ x y, |g x-g y| ≤ C*|x-y|) (hf : Tendsto f l (𝓝 a)) :
    Tendsto g l (𝓝 0) := by
  rcases hl with rfl | rfl
  · exact derivative_tendsto_zero_atTop hd hC hLip hf
  · exact derivative_tendsto_zero_atBot hd hC hLip hf

def acceleration (z : ℝ → TranslatorState) (s : ℝ) : ℝ :=
  -(z s 1)^3/2 + Real.sin (z s 0)
def stressX (z : ℝ → TranslatorState) (s : ℝ) : ℝ :=
  -z s 2 * Real.sin (z s 0) + (z s 1)^2/2 * Real.cos (z s 0)
def sineRate (z : ℝ → TranslatorState) (s : ℝ) : ℝ := z s 1 * Real.cos (z s 0)
def sineAcceleration (z : ℝ → TranslatorState) (s : ℝ) : ℝ :=
  z s 2 * Real.cos (z s 0) - (z s 1)^2 * Real.sin (z s 0)

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)
include hz

theorem stressX_hasDerivAt (s : ℝ) :
    HasDerivAt (stressX z) (-(Real.sin (z s 0))^2) s := by
  have ht := TranslatorGeometry.theta_hasDerivAt hz s
  have hk := TranslatorGeometry.curvature_hasDerivAt hz s
  have hv := TranslatorGeometry.curvatureDerivative_hasDerivAt hz s
  convert (hv.neg.mul ht.sin).add (((hk.pow 2).div_const 2).mul ht.cos) using 1 <;>
    first | rfl | (simp only [Pi.pow_apply, Pi.neg_apply]; ring)

theorem stressX_antitone : Antitone (stressX z) :=
  antitone_of_hasDerivAt_nonpos (stressX_hasDerivAt hz)
    (fun _ => neg_nonpos.mpr (sq_nonneg _))

theorem stressXRate_hasDerivAt (s : ℝ) :
    HasDerivAt (fun u => -(Real.sin (z u 0))^2)
      (-2 * Real.sin (z s 0) * Real.cos (z s 0) * z s 1) s := by
  convert (((TranslatorGeometry.theta_hasDerivAt hz s).sin).pow 2).neg using 1 <;>
    first | rfl | ring

theorem sine_hasDerivAt (s : ℝ) :
    HasDerivAt (fun u => Real.sin (z u 0)) (sineRate z s) s := by
  simpa only [sineRate, mul_comm] using (TranslatorGeometry.theta_hasDerivAt hz s).sin

theorem sineRate_hasDerivAt (s : ℝ) :
    HasDerivAt (sineRate z) (sineAcceleration z s) s := by
  convert (TranslatorGeometry.curvature_hasDerivAt hz s).mul
    (TranslatorGeometry.theta_hasDerivAt hz s).cos using 1 <;>
    first | rfl | (dsimp [sineAcceleration]; ring)

omit hz in
theorem acceleration_abs_le {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) (s : ℝ) :
    |acceleration z s| ≤ K^3/2+1 := by
  have hp : |z s 1|^3 ≤ K^3 := pow_le_pow_left₀ (abs_nonneg _) (hK s) 3
  calc
    _ ≤ |-(z s 1)^3/2| + |Real.sin (z s 0)| := abs_add_le _ _
    _ = |z s 1|^3/2 + |Real.sin (z s 0)| := by simp [abs_div, abs_pow]
    _ ≤ _ := by linarith [Real.abs_sin_le_one (z s 0)]

theorem velocity_abs_le {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) (s : ℝ) :
    |z s 2| ≤ 2*K + (K^3/2+1) :=
  derivative_bound_of_bounded_and_second
    (TranslatorGeometry.curvature_hasDerivAt hz)
    (TranslatorGeometry.curvatureDerivative_hasDerivAt hz) hK
    (acceleration_abs_le hK) s

theorem stressX_abs_le {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) (s : ℝ) :
    |stressX z s| ≤ 2*K+(K^3/2+1)+K^2/2 := by
  have hk : (z s 1)^2 ≤ K^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hK s) 2
  calc
    _ ≤ |-z s 2 * Real.sin (z s 0)| + |(z s 1)^2/2 * Real.cos (z s 0)| := abs_add_le _ _
    _ = |z s 2| * |Real.sin (z s 0)| + ((z s 1)^2/2) * |Real.cos (z s 0)| := by
      simp [abs_mul, abs_div, abs_pow, sq_abs]
    _ ≤ |z s 2| * 1 + ((z s 1)^2/2) * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity))
    _ ≤ _ := by linarith [velocity_abs_le hz hK s]

omit hz in
theorem stressXRate_derivative_abs_le {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) (s : ℝ) :
    |-2 * Real.sin (z s 0) * Real.cos (z s 0) * z s 1| ≤ 2*K := by
  have hh : |Real.sin (z s 0)| * |Real.cos (z s 0)| ≤ 1 := by
    simpa using mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
      (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  calc
    _ = 2 * (|Real.sin (z s 0)| * |Real.cos (z s 0)|) * |z s 1| := by
      rw [abs_mul, abs_mul, abs_mul]
      rw [show |(-2:ℝ)| = 2 by norm_num]
      ring
    _ ≤ (2*1)*K := mul_le_mul (by linarith) (hK s) (abs_nonneg _) (by norm_num)
    _ = _ := by ring

theorem sineAcceleration_abs_le {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) (s : ℝ) :
    |sineAcceleration z s| ≤ 2*K+(K^3/2+1)+K^2 := by
  have hk : (z s 1)^2 ≤ K^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hK s) 2
  calc
    _ ≤ |z s 2 * Real.cos (z s 0)| + |(z s 1)^2 * Real.sin (z s 0)| := abs_sub _ _
    _ = |z s 2| * |Real.cos (z s 0)| + (z s 1)^2 * |Real.sin (z s 0)| := by
      simp [abs_mul, abs_pow, sq_abs]
    _ ≤ |z s 2| * 1 + (z s 1)^2 * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (sq_nonneg _))
    _ ≤ _ := by linarith [velocity_abs_le hz hK s]

omit hz in
theorem stressX_abs_le_velocity_curvature (s : ℝ) :
    |stressX z s| ≤ |z s 2|+(z s 1)^2/2 := by
  calc
    _ ≤ |-z s 2 * Real.sin (z s 0)| + |(z s 1)^2/2 * Real.cos (z s 0)| := abs_add_le _ _
    _ = |z s 2| * |Real.sin (z s 0)| + ((z s 1)^2/2) * |Real.cos (z s 0)| := by
      simp [abs_mul, abs_div, abs_pow, sq_abs]
    _ ≤ |z s 2| * 1 + ((z s 1)^2/2) * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity))
    _ = _ := by ring

theorem stressX_finite_limits {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) :
    (∃ a, Tendsto (stressX z) atTop (𝓝 a)) ∧
      (∃ b, Tendsto (stressX z) atBot (𝓝 b)) := by
  let B := 2*K+(K^3/2+1)+K^2/2
  have hb : BddBelow (range (stressX z)) := by
    refine ⟨-B, ?_⟩
    rintro y ⟨s, rfl⟩
    exact (abs_le.mp (stressX_abs_le hz hK s)).1
  have ha : BddAbove (range (stressX z)) := by
    refine ⟨B, ?_⟩
    rintro y ⟨s, rfl⟩
    exact (abs_le.mp (stressX_abs_le hz hK s)).2
  exact ⟨⟨_, tendsto_atTop_ciInf (stressX_antitone hz) hb⟩,
    ⟨_, tendsto_atBot_ciSup (stressX_antitone hz) ha⟩⟩

omit hz in
theorem curvature_tendsto_zero_of_sine_rate {l : Filter ℝ} {K : ℝ}
    (hK : ∀ s, |z s 1| ≤ K)
    (hsin : Tendsto (fun s => Real.sin (z s 0)) l (𝓝 0))
    (hrate : Tendsto (sineRate z) l (𝓝 0)) : Tendsto (fun s => z s 1) l (𝓝 0) := by
  have hksin : Tendsto (fun s => z s 1 * Real.sin (z s 0)) l (𝓝 0) := by
    have hlim : Tendsto (fun s => K * |Real.sin (z s 0)|) l (𝓝 0) := by
      simpa only [abs_zero, mul_zero] using hsin.abs.const_mul K
    refine squeeze_zero_norm (fun s => ?_) hlim
    ·
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hK s) (abs_nonneg _)
  have hsum := (hksin.pow 2).add (hrate.pow 2)
  have he (s : ℝ) : (z s 1 * Real.sin (z s 0))^2+(sineRate z s)^2 = (z s 1)^2 := by
    calc
      _ = (z s 1)^2 * (Real.sin (z s 0)^2+Real.cos (z s 0)^2) := by
        dsimp [sineRate]
        ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
  apply tendsto_zero_of_square
  simpa only [he, zero_pow (by decide : 2 ≠ 0), zero_add] using hsum

omit hz in
theorem stressX_tendsto_zero_of_state {l : Filter ℝ}
    (hk : Tendsto (fun s => z s 1) l (𝓝 0))
    (hv : Tendsto (fun s => z s 2) l (𝓝 0)) : Tendsto (stressX z) l (𝓝 0) := by
  have hlim : Tendsto (fun s => |z s 2|+(z s 1)^2/2) l (𝓝 0) := by
    simpa only [abs_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] using
      hv.abs.add ((hk.pow 2).div_const 2)
  exact squeeze_zero_norm (stressX_abs_le_velocity_curvature (z := z)) hlim

/-- Every finite stress limit at either spatial end is forced to be zero by
the actual equations and the bound on curvature alone. -/
theorem stressX_zero_limit_end {K a : ℝ} {l : Filter ℝ}
    (hK : ∀ s, |z s 1| ≤ K) (hl : l = atTop ∨ l = atBot)
    (hP : Tendsto (stressX z) l (𝓝 a)) : Tendsto (stressX z) l (𝓝 0) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hPrate : Tendsto (fun s => -(Real.sin (z s 0))^2) l (𝓝 0) :=
    derivative_tendsto_zero_end (C := 2*K) hl (stressX_hasDerivAt hz) (by positivity)
      (lipschitz_bound_of_derivative_bound (stressXRate_hasDerivAt hz)
        (stressXRate_derivative_abs_le hK)) hP
  have hsin : Tendsto (fun s => Real.sin (z s 0)) l (𝓝 0) := by
    apply tendsto_zero_of_square
    simpa only [neg_neg, neg_zero] using hPrate.neg
  have hrate : Tendsto (sineRate z) l (𝓝 0) :=
    derivative_tendsto_zero_end (C := 2*K+(K^3/2+1)+K^2) hl (sine_hasDerivAt hz)
      (by positivity)
      (lipschitz_bound_of_derivative_bound (sineRate_hasDerivAt hz)
        (sineAcceleration_abs_le hz hK)) hsin
  have hk := curvature_tendsto_zero_of_sine_rate hK hsin hrate
  have hv : Tendsto (fun s => z s 2) l (𝓝 0) :=
    derivative_tendsto_zero_end (C := K^3/2+1) hl
      (TranslatorGeometry.curvature_hasDerivAt hz) (by positivity)
      (lipschitz_bound_of_derivative_bound
        (TranslatorGeometry.curvatureDerivative_hasDerivAt hz)
        (acceleration_abs_le hK)) hk
  exact stressX_tendsto_zero_of_state hk hv

/-- Actual global normalized translator solutions with globally bounded
curvature have identically zero curvature and identically zero normal force.
No velocity bound, stress identity, endpoint limit or integrability is assumed. -/
theorem bounded_curvature_rigidity {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) :
    (∀ s, z s 1 = 0) ∧ (∀ s, Real.sin (z s 0) = 0) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := stressX_finite_limits hz hK
  have htop := stressX_zero_limit_end hz hK (Or.inl rfl) ha
  have hbot := stressX_zero_limit_end hz hK (Or.inr rfl) hb
  have hPzero : stressX z = fun _ => 0 := by
    funext s
    exact le_antisymm ((stressX_antitone hz).ge_of_tendsto hbot s)
      ((stressX_antitone hz).le_of_tendsto htop s)
  have hsin (s : ℝ) : Real.sin (z s 0) = 0 := by
    have hd := stressX_hasDerivAt hz s
    rw [hPzero] at hd
    have hh := hd.unique (hasDerivAt_const s (0:ℝ))
    exact sq_eq_zero_iff.mp (neg_eq_zero.mp hh)
  refine ⟨?_, hsin⟩
  intro s
  have hsfun : (fun u => Real.sin (z u 0)) = fun _ => (0:ℝ) := funext hsin
  have hd := sine_hasDerivAt hz s
  rw [hsfun] at hd
  have hrate : z s 1 * Real.cos (z s 0) = 0 := hd.unique (hasDerivAt_const s (0:ℝ))
  have hcos : Real.cos (z s 0) ≠ 0 := by
    intro hc
    have htrig := Real.sin_sq_add_cos_sq (z s 0)
    rw [hsin s, hc] at htrig
    norm_num at htrig
  exact (mul_eq_zero.mp hrate).resolve_right hcos

/-- The actual integrated position is a straight line parallel to the
translation vector (1,0), with its orientation represented by c^2=1. -/
theorem bounded_curvature_position_line {K : ℝ} (hK : ∀ s, |z s 1| ≤ K) :
    ∃ c : ℝ, c^2 = 1 ∧ ∀ s,
      TranslatorGeometry.betaX z s = c*s ∧ TranslatorGeometry.betaY z s = 0 := by
  have hr := bounded_curvature_rigidity hz hK
  have htheta (s : ℝ) : z s 0 = z 0 0 :=
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun u _ => (TranslatorGeometry.theta_hasDerivAt hz u).differentiableAt.differentiableWithinAt)
      (fun u _ => by rw [(TranslatorGeometry.theta_hasDerivAt hz u).deriv, hr.1 u]; rfl)
      (mem_univ s) (mem_univ 0)
  refine ⟨Real.cos (z 0 0), ?_, ?_⟩
  · have ht := Real.sin_sq_add_cos_sq (z 0 0)
    simpa only [hr.2 0, zero_pow (by decide : 2 ≠ 0), zero_add] using ht
  · intro s
    constructor
    · simp only [TranslatorGeometry.betaX, htheta, intervalIntegral.integral_const,
        sub_zero, smul_eq_mul]
      ring
    · simp [TranslatorGeometry.betaY, hr.2]

theorem initial_curvature_unbounded (h0 : z 0 = ![Real.pi/2, 1, 0]) :
    ∀ K : ℝ, ∃ s : ℝ, K < |z s 1| := by
  intro K
  by_contra hnot
  have hK : ∀ s, |z s 1| ≤ K := fun s => le_of_not_gt (fun hs => hnot ⟨s, hs⟩)
  have hh := (bounded_curvature_rigidity hz hK).1 0
  simp [h0] at hh

omit hz in
/-- The actual nonstraight example from the specified initial data has
unbounded curvature; the full existence theorem supplies the witness. -/
theorem exists_unbounded_curvature_translator : ∃ z : ℝ → TranslatorState,
    z 0 = ![Real.pi/2, 1, 0] ∧
    (∀ s, HasDerivAt z (translatorNumerator (z s)) s) ∧
    ∀ K : ℝ, ∃ s : ℝ, K < |z s 1| := by
  obtain ⟨z, hz0, hz⟩ := exists_global_translator ![Real.pi/2, 1, 0]
  exact ⟨z, hz0, hz, initial_curvature_unbounded hz hz0⟩

end
end OpenTranslator.BoundedCurvature

#print axioms OpenTranslator.BoundedCurvature.bounded_curvature_rigidity
#print axioms OpenTranslator.BoundedCurvature.exists_unbounded_curvature_translator

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"BoundedCurvature: audited {checked} declarations; standard axioms only."
