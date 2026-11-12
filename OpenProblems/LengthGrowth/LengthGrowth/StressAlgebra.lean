import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-!
# Algebraic constants for the actual elastic-stress proof

These helpers do not assert a coercivity theorem for curves. The separate
geometric proof must supply the displayed integral inequalities, the stress
magnitude comparison, and the closing integral. No other open-problem
project is imported here.
-/
namespace LengthGrowth.StressAlgebra
noncomputable section
set_option maxHeartbeats 2000000

lemma sqrt_two_le_three_halves : Real.sqrt 2≤(3/2:ℝ) := by
  apply (Real.sqrt_le_iff).2
  norm_num

/-- Even the weaker constant4, sufficient for the elementary closing-energy
bound used by the geometric proof, gives the same threshold64. -/
theorem ratio_lt64 {x r : ℝ} (hx : 0≤x) (_hr : 0≤r) (hr1 : r≤1)
    (hquad : x^2≤4+2*Real.sqrt 2*Real.sqrt (x^2+Real.sqrt 2*r*x^3)) : x<64 := by
  by_contra hn
  have hx64 : 64≤x := le_of_not_gt hn
  have hc0 := Real.sqrt_nonneg (2:ℝ)
  have hc2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsmall : 1+Real.sqrt 2*r*x≤2*x := by
    have h1 := mul_le_mul_of_nonneg_left hr1 hc0
    have h2 := mul_le_mul_of_nonneg_right h1 hx
    have h3 := mul_le_mul_of_nonneg_right sqrt_two_le_three_halves hx
    nlinarith
  have hz : x^2+Real.sqrt 2*r*x^3≤2*x^3 := by
    have hm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg x)
    nlinarith
  have hroot : Real.sqrt (x^2+Real.sqrt 2*r*x^3)≤
      Real.sqrt 2*x*Real.sqrt x := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity,?_⟩
    have he : (Real.sqrt 2*x*Real.sqrt x)^2=2*x^3 := by
      calc
        _ = (Real.sqrt 2)^2*x^2*(Real.sqrt x)^2 := by ring
        _ = 2*x^3 := by rw [hc2,Real.sq_sqrt hx]; ring
    rw [he]
    exact hz
  have hsx : Real.sqrt x≤x/8 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity,?_⟩
    have hm := mul_nonneg hx (sub_nonneg.mpr hx64)
    nlinarith
  have hlast : Real.sqrt (x^2+Real.sqrt 2*r*x^3)≤Real.sqrt 2*x*(x/8) :=
    hroot.trans (mul_le_mul_of_nonneg_left hsx (mul_nonneg hc0 hx))
  have hmul := mul_le_mul_of_nonneg_left hlast (show 0≤2*Real.sqrt (2:ℝ) by positivity)
  have he : 2*Real.sqrt 2*(Real.sqrt 2*x*(x/8))=x^2/2 := by
    calc
      _ = (Real.sqrt 2)^2*x^2/4 := by ring
      _ = x^2/2 := by rw [hc2]; ring
  rw [he] at hmul
  nlinarith [sq_nonneg (x-64)]

/-- Bounds on the actual stress magnitude follow from its squared variation. -/
theorem stress_norm_bounds {w M r : ℝ} (hw : 0≤w) (hM : 0≤M)
    (hr : r≤1/4096) (hvariation : |w^2-M^4/4|≤4*r*M^4) :
    M^2/4≤w ∧ w≤M^2 := by
  have h4 : 0≤M^4 := pow_nonneg hM 4
  have hr4 := mul_le_mul_of_nonneg_right hr h4
  obtain ⟨hlo,hhi⟩ := abs_le.mp hvariation
  constructor
  · apply (sq_le_sq₀ (by positivity) hw).mp
    nlinarith
  · apply le_of_sq_le_sq _ (sq_nonneg M)
    nlinarith

theorem unit_stress_variation_lt_half {r : ℝ} (hr : r≤1/4096) :
    8*Real.sqrt 2*r<1/2 := by
  have h := mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg (2:ℝ))
  nlinarith [sqrt_two_le_three_halves]

theorem closing_factor_lt_one {r x : ℝ} (hr0 : 0≤r) (hr : r≤1/4096)
    (hx : x<64) : 32*Real.sqrt 2*r*x<1 := by
  have h1 := mul_le_mul_of_nonneg_left hx.le hr0
  have hrx : r*x≤1/64 := by linarith
  have h2 := mul_le_mul_of_nonneg_left hrx (Real.sqrt_nonneg (2:ℝ))
  nlinarith [sqrt_two_le_three_halves]

/-- The actual curvature-derivative L2 bound, once the geometric integral
estimate and the two normalized ratio estimates have been established. -/
theorem curvature_derivative_bound {E M D B : ℝ} (hE : 0<E) (hM : 0<M)
    (hgradient : B^2≤E*M^2+Real.sqrt (2*E*D))
    (hr : Real.sqrt (E*D)/M^3≤1/4096) (hx : M/E<64) :
    B≤2*Real.sqrt E*M := by
  have hMr : M<64*E := (div_lt_iff₀ hE).mp hx
  have hM3 : M^3≤64*E*M^2 := by
    have hh := mul_le_mul_of_nonneg_right hMr.le (sq_nonneg M)
    nlinarith
  have hsr : Real.sqrt (E*D)≤M^3/4096 := by
    have hh := (div_le_iff₀ (pow_pos hM 3)).mp hr
    linarith
  have hs : Real.sqrt (E*D)≤E*M^2/64 := by linarith
  have hroot : Real.sqrt (2*E*D)≤(3/2)*(E*M^2/64) := by
    rw [show 2*E*D=2*(E*D) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul sqrt_two_le_three_halves hs (Real.sqrt_nonneg _) (by norm_num)
  have hsquare : B^2≤4*E*M^2 := by
    nlinarith [mul_nonneg hE.le (sq_nonneg M)]
  apply le_of_sq_le_sq _ (by positivity : 0≤2*Real.sqrt E*M)
  have he : (2*Real.sqrt E*M)^2=4*E*M^2 := by
    calc
      _ = 4*(Real.sqrt E)^2*M^2 := by ring
      _ = 4*E*M^2 := by rw [Real.sq_sqrt hE.le]
  rwa [he]

end
end LengthGrowth.StressAlgebra

#print axioms LengthGrowth.StressAlgebra.ratio_lt64
#print axioms LengthGrowth.StressAlgebra.curvature_derivative_bound

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.StressAlgebra).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Stress algebra audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Stress algebra audit passed for {count} declarations."
