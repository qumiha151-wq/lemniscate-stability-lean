import Lemniscate.Algebra

/-! A polynomial proof of the infinite-row quartic cutoff argument.
The hypotheses are precisely the leading sign and the first two derivative
checks at the cutoff; every real argument beyond the cutoff is covered.
-/
namespace Lemniscate

def shiftedQuartic (c shift a b d x : ℝ) : ℝ := -c*(x-shift)^4+a*x^2+b*x+d

theorem shiftedQuartic_expansion (c shift a b d x h : ℝ) :
    shiftedQuartic c shift a b d (x+h) =
      shiftedQuartic c shift a b d x +
      (-4*c*(x-shift)^3+2*a*x+b)*h +
      (-6*c*(x-shift)^2+a)*h^2 -4*c*(x-shift)*h^3-c*h^4 := by
  unfold shiftedQuartic
  ring

theorem shiftedQuartic_beyond_cutoff (c shift a b d cutoff x : ℝ)
    (hc : 0 ≤ c) (hcut : shift ≤ cutoff) (hx : cutoff ≤ x)
    (hfirst : -4*c*(cutoff-shift)^3+2*a*cutoff+b ≤ 0)
    (hsecond : -6*c*(cutoff-shift)^2+a ≤ 0) :
    shiftedQuartic c shift a b d x ≤ shiftedQuartic c shift a b d cutoff := by
  let h := x-cutoff
  have hh : 0 ≤ h := sub_nonneg.mpr hx
  have hx' : x = cutoff+h := by dsimp [h]; ring
  rw [hx', shiftedQuartic_expansion]
  have h1 := mul_nonpos_of_nonpos_of_nonneg hfirst hh
  have h2 := mul_nonpos_of_nonpos_of_nonneg hsecond (sq_nonneg h)
  have h3 : 0 ≤ 4*c*(cutoff-shift)*h^3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) (sub_nonneg.mpr hcut))
      (pow_nonneg hh _)
  have h4 : 0 ≤ c*h^4 := mul_nonneg hc (pow_nonneg hh _)
  linarith

theorem shiftedQuartic_uniform_bound (c shift a b d cutoff bound : ℝ)
    (hc : 0 ≤ c) (hcut : shift ≤ cutoff)
    (hfirst : -4*c*(cutoff-shift)^3+2*a*cutoff+b ≤ 0)
    (hsecond : -6*c*(cutoff-shift)^2+a ≤ 0)
    (hbase : shiftedQuartic c shift a b d cutoff < bound) :
    ∀ x ≥ cutoff, shiftedQuartic c shift a b d x < bound := by
  intro x hx
  exact (shiftedQuartic_beyond_cutoff c shift a b d cutoff x hc hcut hx hfirst hsecond).trans_lt hbase

end Lemniscate
