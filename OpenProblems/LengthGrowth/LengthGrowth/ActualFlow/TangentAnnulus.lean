import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
namespace LengthGrowth.TangentSpectrum
open Real
noncomputable section
def band (X z : ℝ) : Prop := X/128<z ∧ z≤64*X^2
instance (X z : ℝ) : Decidable (band X z) := by unfold band;infer_instance
def bandMass (X : ℝ) (w b : ℤ→ℝ) (n : ℤ) : ℝ :=
  if band X (w n) then √(w n)*b n else 0

theorem band_escape {X A B C D : ℝ} {w b : ℤ→ℝ} (xp : 0<X)
    (weights : ∀n,0≤w n) (mass : ∀n,0≤b n)
    (zero : HasSum b A) (first : HasSum (fun n=>w n*b n) B)
    (fourth : HasSum (fun n=>w n^4*b n) C)
    (inside : HasSum (bandMass X w b) D)
    (total : A≤1) (one : 3*X/128≤B) (four : C≤1024*X^7) :
    3/2048≤D := by
  let upper := 64*X^2
  have hi : 0<upper := by unfold upper;positivity
  have pt (n : ℤ) : w n*b n≤(X/128)*b n+(upper^3)⁻¹*(w n^4*b n)+(8*X)*bandMass X w b n := by
    have cap : 0≤(upper^3)⁻¹*(w n^4*b n) := mul_nonneg (by positivity) (mul_nonneg (by positivity) (mass n))
    by_cases low : w n≤X/128
    · have h : ¬band X (w n) := fun z=>not_lt_of_ge low z.1
      simp only [bandMass,if_neg h,mul_zero,add_zero]
      exact (mul_le_mul_of_nonneg_right low (mass n)).trans (le_add_of_nonneg_right cap)
    · by_cases inhi : w n≤upper
      · have h : band X (w n) := ⟨lt_of_not_ge low,inhi⟩
        simp only [bandMass,if_pos h]
        have s : √(w n)≤8*X := by
          apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
          rw [Real.sq_sqrt (weights n)]
          exact inhi.trans_eq (by unfold upper;ring)
        have q := mul_le_mul_of_nonneg_right s (mul_nonneg (sqrt_nonneg (w n)) (mass n))
        have e := Real.sq_sqrt (weights n)
        have id : √(w n)*(√(w n)*b n)=w n*b n := by rw [←mul_assoc,←sq,e]
        rw [id] at q
        linarith only [q,cap,mul_nonneg (by positivity : 0≤X/128) (mass n)]
      · have h : ¬band X (w n) := fun z=>inhi z.2
        simp only [bandMass,if_neg h,mul_zero,add_zero]
        have high := lt_of_not_ge inhi
        have pow := pow_le_pow_left₀ hi.le high.le 3
        have scale : w n ≤ (upper^3)⁻¹*w n^4 := by
          rw [inv_mul_eq_div]
          apply (le_div_iff₀ (pow_pos hi 3)).mpr
          simpa only [pow_succ (w n) 3,mul_comm (w n) _] using (mul_le_mul_of_nonneg_right pow (weights n))
        have scaled := mul_le_mul_of_nonneg_right scale (mass n)
        rw [mul_assoc] at scaled
        exact scaled.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) (mass n)))
  have cmp := hasSum_le pt first (((zero.mul_left (X/128)).add (fourth.mul_left (upper^3)⁻¹)).add (inside.mul_left (8*X)))
  have lo := mul_le_mul_of_nonneg_left total (show 0≤X/128 by positivity)
  have up := mul_le_mul_of_nonneg_left four (show 0≤(upper^3)⁻¹ by positivity)
  have eq : (upper^3)⁻¹*(1024*X^7)=X/256 := by dsimp [upper];field_simp;ring
  rw [eq] at up
  apply le_of_mul_le_mul_right (a:=X) _ xp
  nlinarith only [lo,up,one,cmp]
end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.band_escape
