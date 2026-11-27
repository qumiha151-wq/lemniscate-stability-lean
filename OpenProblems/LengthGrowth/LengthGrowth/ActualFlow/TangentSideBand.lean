import LengthGrowth.ActualFlow.TangentAnnulus
import LengthGrowth.ActualFlow.TangentMomentInequality
namespace LengthGrowth.TangentSpectrum
noncomputable section
open Real

/-- A frequency projection on one of the two half-lines. The sign at zero is immaterial. -/
def cut (side : ℤ→Prop) [DecidablePred side] (b : ℤ→ℝ) (n : ℤ) : ℝ := if side n then b n else 0

theorem side_band {b w v : ℤ→ℝ} {S X M : ℝ} (side : ℤ→Prop) [DecidablePred side]
    (xp : 0<X) (hw : ∀n,0≤w n) (hb : ∀n,0≤b n)
    (sign : ∀n,v n=if side n then w n else -w n)
    (zero : HasSum b 1) (signed : HasSum (fun n=>v n*b n) S)
    (two : HasSum (fun n=>w n^2*b n) (2*X^3))
    (four : HasSum (fun n=>w n^4*b n) M) (cap : M≤1024*X^7) (small : |S|≤X/64) :
    3/2048≤∑' n,bandMass X w (cut side b) n := by
  have cn (n : ℤ) : 0≤cut side b n := by unfold cut;split <;> simp [hb]
  have cb (n : ℤ) : cut side b n≤b n := by unfold cut;split <;> simp [hb]
  have wn (n : ℤ) : 0≤w n*b n := mul_nonneg (hw n) (hb n)
  have w4 (n : ℤ) : 0≤w n^4 := by positivity
  have comp (n : ℤ) : w n*b n≤b n+w n^2*b n := by
    have p : w n≤1+w n^2 := by nlinarith [sq_nonneg (w n-1)]
    simpa only [add_mul,one_mul] using mul_le_mul_of_nonneg_right p (hb n)
  have whole : Summable (fun n=>w n*b n) := Summable.of_nonneg_of_le wn comp (zero.add two).summable
  have first := whole.hasSum
  have interp := moment_gap hw hb first two four
  let A := ∑'n,w n*b n
  have an : 0≤A := first.nonneg wn
  have g : X^2≤128*A^2 := by
    apply le_of_mul_le_mul_right (a:=X^7) _ (pow_pos xp 7)
    change (2*X^3)^3≤A^2*M at interp
    nlinarith only [interp,mul_le_mul_of_nonneg_left cap (sq_nonneg A)]
  have la : X≤16*A := by
    apply (sq_le_sq₀ xp.le (mul_nonneg (by norm_num) an)).mp
    nlinarith only [g,sq_nonneg A]
  have cut0 : Summable (cut side b) := Summable.of_nonneg_of_le cn cb zero.summable
  have cut1 : Summable (fun n=>w n*cut side b n) := Summable.of_nonneg_of_le (fun n=>mul_nonneg (hw n) (cn n))
    (fun n=>mul_le_mul_of_nonneg_left (cb n) (hw n)) whole
  have cut4 : Summable (fun n=>w n^4*cut side b n) := Summable.of_nonneg_of_le (fun n=>mul_nonneg (w4 n) (cn n))
    (fun n=>mul_le_mul_of_nonneg_left (cb n) (w4 n)) four.summable
  have splitEq : HasSum (fun n=>v n*b n) (2*(∑'n,w n*cut side b n)-A) := by
    convert! (cut1.hasSum.mul_left 2).sub first using 1
    funext n;rw [sign];unfold cut;split <;> ring
  have eq := splitEq.unique signed
  have low : 3*X/128≤∑'n,w n*cut side b n := by linarith only [eq,la,neg_le_of_abs_le small]
  have bd (n : ℤ) : bandMass X w (cut side b) n≤cut side b n+w n*cut side b n := by
    unfold bandMass
    split
    · have h : √(w n)≤1+w n := by nlinarith only [Real.sq_sqrt (hw n),sq_nonneg (√(w n)-1)]
      simpa only [add_mul,one_mul] using mul_le_mul_of_nonneg_right h (cn n)
    · exact add_nonneg (cn n) (mul_nonneg (hw n) (cn n))
  have bn (n : ℤ) : 0≤bandMass X w (cut side b) n := by
    unfold bandMass;split <;> first | exact mul_nonneg (sqrt_nonneg _) (cn n) | exact le_rfl
  have inside := Summable.of_nonneg_of_le bn bd (cut0.add cut1)
  exact band_escape xp hw cn cut0.hasSum cut1.hasSum cut4.hasSum inside.hasSum
    (hasSum_le cb cut0.hasSum zero) low ((hasSum_le (fun n=>mul_le_mul_of_nonneg_left (cb n) (w4 n)) cut4.hasSum four).trans cap)
end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.side_band
