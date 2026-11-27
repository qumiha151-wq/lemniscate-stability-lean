import LengthGrowth.ActualFlow.TangentSideBand
import LengthGrowth.ActualFlow.TangentFourierMoment
namespace LengthGrowth.TangentSpectrum
noncomputable section
open Real
def side (positive : Bool) (n : ℤ) : Prop := if positive then 0≤omega n else omega n≤0
instance (positive : Bool) : DecidablePred (side positive) := fun n=>by unfold side;split <;> infer_instance
def signedOmega (positive : Bool) (n : ℤ) := if positive then omega n else -omega n
def halfEnergy (positive : Bool) (T : ℝ→ℂ) := cut (side positive) (energy T)
def tailDensity (W : ℝ) (positive : Bool) (T : ℝ→ℂ) (n : ℤ) :=
  if W < |omega n| then Real.sqrt (abs (omega n)) * halfEnergy positive T n else 0
def tail (W : ℝ) (positive : Bool) (T : ℝ→ℂ) := ∑'n,tailDensity W positive T n

theorem tail_escape {T : ℝ→ℂ} {S M X W : ℝ} (xp : 0<X) (cutoff : W≤X/128)
    (small : |S|≤X/64)
    (zero : HasSum (energy T) 1) (signed : HasSum (fun n=>omega n*energy T n) S)
    (two : HasSum (fun n=>|omega n|^2*energy T n) (2*X^3))
    (four : HasSum (fun n=>|omega n|^4*energy T n) M) (cap : M≤1024*X^7)
    (positive : Bool) : 3/2048≤tail W positive T := by
  let w := fun n=>|omega n|
  let b := energy T
  let z := if positive then S else -S
  have hs : HasSum (fun n=>signedOmega positive n*b n) z := by
    cases positive
    · simpa [signedOmega,z] using signed.neg
    · exact signed
  have sign (n : ℤ) : signedOmega positive n=if side positive n then w n else -w n := by
    dsimp [w];cases positive
    · simp only [signedOmega,side,Bool.false_eq_true,if_false]
      split
      next h=>rw [abs_of_nonpos h]
      next h=>rw [abs_of_nonneg (le_of_not_ge h)]
    · simp only [signedOmega,side,if_true]
      split
      next h=>rw [abs_of_nonneg h]
      next h=>rw [abs_of_nonpos (le_of_not_ge h),neg_neg]
  have absz : |z|≤X/64 := by cases positive <;> simpa [z] using small
  have hb (n : ℤ) : 0≤b n := sq_nonneg _
  have h := side_band (side positive) xp (fun n=>abs_nonneg (omega n)) hb sign zero hs two four cap absz
  have cb (n : ℤ) : 0≤halfEnergy positive T n := by
    unfold halfEnergy cut;split <;> first | exact hb n | exact le_rfl
  have ub (n : ℤ) : halfEnergy positive T n≤b n := by
    unfold halfEnergy cut;split <;> first | exact hb n | exact le_rfl
  have tdnon (n : ℤ) : 0≤tailDensity W positive T n := by
    unfold tailDensity;split <;> first | exact mul_nonneg (sqrt_nonneg _) (cb n) | exact le_rfl
  have td (n : ℤ) : tailDensity W positive T n≤b n+w n^2*b n := by
    have wb := mul_le_mul_of_nonneg_left (ub n) (sqrt_nonneg (w n))
    have s1 : √(w n)≤1+w n^2 := by
      have q := Real.sq_sqrt (abs_nonneg (omega n))
      change √(w n)^2=w n at q
      nlinarith only [q,sq_nonneg (√(w n)-1),sq_nonneg (w n-1/2)]
    unfold tailDensity
    split
    · calc
        _ ≤ √(w n)*b n := wb
        _ ≤ (1+w n^2)*b n := mul_le_mul_of_nonneg_right s1 (hb n)
        _ = _ := by ring
    · exact add_nonneg (hb n) (mul_nonneg (sq_nonneg _) (hb n))
  have tsum := Summable.of_nonneg_of_le tdnon td (zero.add two).summable
  have cmp (n : ℤ) : bandMass X w (cut (side positive) b) n≤tailDensity W positive T n := by
    unfold bandMass;split
    next bh =>
      have lo : W < |omega n| := lt_of_le_of_lt cutoff bh.1
      rw [tailDensity,if_pos lo]
      exact le_rfl
    next => exact tdnon n
  have bn (n : ℤ) : 0≤bandMass X w (cut (side positive) b) n := by
    unfold bandMass;split <;> first | exact mul_nonneg (sqrt_nonneg _) (cb n) | exact le_rfl
  have bs:=Summable.of_nonneg_of_le bn cmp tsum
  exact h.trans (hasSum_le cmp bs.hasSum tsum.hasSum)
end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.tail_escape
