import SolitonClassification.CentreShotEntry
import SolitonClassification.OuterDescent

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress.Data
variable {δ : ℝ} (z : Data δ)

def positionSquared (x : ℝ) := z.p x^2+z.q x^2

theorem positionSquared_derivative (hd : 0<δ) (x : ℝ) :
    HasDerivAt z.positionSquared (2*z.q x) x := by
  convert! ((z.dp x).pow 2).add ((z.dq x).pow 2) using 1
  field_simp [hd.ne']; ring

theorem tangent_projection_formula {x : ℝ} (hp : 0<z.amplitude x) :
    z.q x = z.shape x^2/2*z.along x-z.slope x*z.across x := by
  unfold shape along slope across
  simp only [div_pow,show z.root x^2=z.amplitude x from Real.sq_sqrt hp.le]
  field_simp [hp.ne']
  unfold radial transverse
  rw [z.amplitude_sq]; ring

/-- A small transverse component prevents loss of radial distance for a
    bounded real time, even at phases where tangential and radial directions
    have negative inner product. -/
theorem radius_during_descent {S T η : ℝ} (hd : 0<δ) (st : S≤T)
    (data : ∀x ∈ Icc S T, 0<z.amplitude x ∧ 0≤z.along x ∧ |z.across x|≤η) :
    z.positionSquared S - 2*η*(T-S) ≤ z.positionSquared T := by
  let f := fun x => z.positionSquared x+2*η*x
  have step (x : ℝ) : HasDerivAt f (2*z.q x+2*η) x := by
    convert! (z.positionSquared_derivative hd x).add ((hasDerivAt_id x).const_mul (2*η)) using 1
    ring
  have mono : MonotoneOn f (Icc S T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x _ => (step x).continuousAt.continuousWithinAt)
      (fun x _ => (step x).differentiableAt.differentiableWithinAt)
    intro x hx
    obtain ⟨P,al,ac⟩ := data x (interior_subset hx)
    have osc := (z.normalized_rates x P hd).oscillator
    have w : |z.slope x|≤1 := le_of_sq_le_sq
      (by rw [sq_abs]; nlinarith [sq_nonneg (z.shape x^2/2)]) zero_le_one
    have cross : z.slope x*z.across x≤η := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul w ac (abs_nonneg _) zero_le_one
    rw [(step x).deriv,z.tangent_projection_formula P]
    nlinarith only [cross,mul_nonneg (sq_nonneg (z.shape x)) al]
  have m := mono (left_mem_Icc.mpr st) (right_mem_Icc.mpr st) st
  dsimp [f] at m
  linarith

end ClosedSimilarity.OuterStress.Data
