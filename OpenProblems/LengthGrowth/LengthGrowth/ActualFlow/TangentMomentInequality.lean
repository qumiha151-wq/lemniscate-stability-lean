import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LengthGrowth.TangentSpectrum
open Real
/-- The log-convex interpolation for the first, second and fourth frequency
moments, proved directly from a nonnegative polynomial. -/
theorem moment_gap {w b : ℤ→ℝ} {M₁ M₂ M₄ : ℝ}
    (hw : ∀n,0≤w n) (hb : ∀n,0≤b n)
    (one : HasSum (fun n=>w n*b n) M₁) (two : HasSum (fun n=>(w n)^2*b n) M₂)
    (four : HasSum (fun n=>(w n)^4*b n) M₄) :
    M₂^3≤M₁^2*M₄ := by
  have test (r : ℝ) (hr : 0≤r) : 0≤M₄-3*r^2*M₂+2*r^3*M₁ := by
    have series := (four.sub (two.mul_left (3*r^2))).add (one.mul_left (2*r^3))
    have pos (n : ℤ) : 0≤w n^4*b n-3*r^2*(w n^2*b n)+2*r^3*(w n*b n) := by
      rw [show w n^4*b n-3*r^2*(w n^2*b n)+2*r^3*(w n*b n)=w n*(w n-r)^2*(w n+2*r)*b n by ring]
      exact mul_nonneg (mul_nonneg (mul_nonneg (hw n) (sq_nonneg _)) (by linarith [hw n])) (hb n)
    exact series.nonneg pos
  have non : 0≤M₁ := one.nonneg fun n=>mul_nonneg (hw n) (hb n)
  have n2 : 0≤M₂ := two.nonneg fun n=>mul_nonneg (sq_nonneg _) (hb n)
  by_cases p : M₁=0
  · have terms : ∀n,w n*b n=0 := fun n=>le_antisymm ((le_hasSum one n fun j _=>mul_nonneg (hw j) (hb j)).trans_eq p)
        (mul_nonneg (hw n) (hb n))
    have all0 : (fun n=>w n^2*b n)=fun _=>0 := by
      funext n;rw [pow_two,mul_assoc,terms,mul_zero]
    rw [all0] at two
    have m := two.unique hasSum_zero
    simp [m,p]
  · have hp := lt_of_le_of_ne non (Ne.symm p)
    have h := test (M₂/M₁) (div_nonneg n2 non)
    field_simp [p] at h
    have g := mul_nonneg (sq_nonneg M₁) non
    nlinarith only [h,g]

/-- Positive and negative signed frequency weights, expressed in angular
frequency units. A record-level geometric fourth moment cap implies a
quantitative lower bound even on the smaller of the two sides. -/
theorem signed_record_lower {b : ℤ→ℝ} {U X P N M₄ : ℝ}
    (hb : ∀n,0≤b n) (hX : 0<X) (scale : X^3=U) (hp : 0≤P) (hn : 0≤N)
    (h1 : HasSum (fun n : ℤ=>|2*pi*(n:ℝ)| *b n) (P+N))
    (h2 : HasSum (fun n : ℤ=>|2*pi*(n:ℝ)|^2*b n) (2*U))
    (h4 : HasSum (fun n : ℤ=>|2*pi*(n:ℝ)|^4*b n) M₄)
    (cap : M₄≤1024*X^7) :
    X≤8*√2*(2*min P N+|P-N|) := by
  have a:=moment_gap (fun _=>abs_nonneg _) hb h1 h2 h4
  have c:=(mul_le_mul_of_nonneg_left cap (sq_nonneg (P+N)))
  have g : X^2≤128*(P+N)^2 := by
    rw [←scale] at a
    apply le_of_mul_le_mul_right (a:=X^7) _ (pow_pos hX 7)
    nlinarith only [a,c]
  have free : 2*min P N+|P-N|=P+N := by
    rcases le_total P N with hh|hh
    · rw [min_eq_left hh,abs_of_nonpos (sub_nonpos.mpr hh)];ring
    · rw [min_eq_right hh,abs_of_nonneg (sub_nonneg.mpr hh)];ring
  rw [free]
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have equality : 128*(P+N)^2=(8*√2*(P+N))^2 := by rw [mul_pow,mul_pow,sq];ring
  apply (sq_le_sq₀ hX.le (by positivity)).mp
  calc
    X^2≤128*(P+N)^2 := g
    _ ≤ (8*√2*(P+N))^2 := equality.le
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.moment_gap
