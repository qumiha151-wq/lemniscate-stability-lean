import SolitonClassification.Rotating.ResetHullFrames

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set
set_option maxHeartbeats 1800000

/-- Rational pairs approximating cosine and sine at successively doubled angles. -/
structure DoubleAngles (q : ℚ) where
  C : ℕ → ℚ
  S : ℕ → ℚ
  phase : |q|≤5
  cos0 : |C 0-(1-(q/2048)^2/2)|≤1/10^14
  sin0 : |S 0-(q/2048-(q/2048)^3/6)|≤1/10^14
  unitC : ∀ i, i≤11 → |C i|≤1
  unitS : ∀ i, i≤11 → |S i|≤1
  cosStep : ∀ i, i<11 → |C (i+1)-((C i)^2-(S i)^2)|≤1/10^14
  sinStep : ∀ i, i<11 → |S (i+1)-2*(S i)*(C i)|≤1/10^14

private theorem product_error {a b c d e : ℝ} (ha : |a|≤1) (hd : |d|≤1)
    (x : |a-c|≤e) (y : |b-d|≤e) : |a*b-c*d|≤2*e := by
  rw [show a*b-c*d=a*(b-d)+(a-c)*d by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  linarith [mul_le_mul ha y (abs_nonneg _) (by norm_num : (0:ℝ)≤1),
    mul_le_mul x hd (abs_nonneg _) (by linarith [abs_nonneg (a-c)] : 0≤e)]

theorem double_angles_sound {q : ℚ} (T : DoubleAngles q) :
    |Real.cos (q:ℝ)-(T.C 11:ℝ)|≤1/10000 ∧ |Real.sin (q:ℝ)-(T.S 11:ℝ)|≤1/10000 := by
  let a : ℝ := (q:ℝ)/2048
  have phase := (Rat.cast_le (K:=ℝ)).mpr T.phase
  push_cast at phase
  have small : |a|≤1/256 := by dsimp [a]; rw [abs_div,abs_of_pos (by norm_num : 0<(2048:ℝ))]; linarith
  let err := fun n : ℕ => (4:ℝ)^n*(2/(10:ℝ)^11)+(4^n-1)/(3*10^14)
  have base : |Real.cos a-(T.C 0:ℝ)|≤err 0 ∧ |Real.sin a-(T.S 0:ℝ)|≤err 0 := by
    have c := Real.cos_bound (small.trans (by norm_num))
    have s := Real.sin_bound (small.trans (by norm_num))
    have hC := (Rat.cast_le (K:=ℝ)).mpr T.cos0
    have hS := (Rat.cast_le (K:=ℝ)).mpr T.sin0
    push_cast at hC hS
    change |(T.C 0:ℝ)-(1-a^2/2)|≤_ at hC
    change |(T.S 0:ℝ)-(a-a^3/6)|≤_ at hS
    rw [abs_sub_comm] at hC hS
    have q4 := pow_le_pow_left₀ (abs_nonneg _) small 4
    have q5 := pow_le_pow_left₀ (abs_nonneg _) small 5
    constructor
    · exact (abs_sub_le (Real.cos a) (1-a^2/2) _).trans (by norm_num [err] at *; linarith)
    · exact (abs_sub_le (Real.sin a) (a-a^3/6) _).trans (by norm_num [err] at *; linarith)
  have all (i : ℕ) (hi : i≤11) :
      |Real.cos ((2:ℝ)^i*a)-(T.C i:ℝ)|≤err i ∧ |Real.sin ((2:ℝ)^i*a)-(T.S i:ℝ)|≤err i := by
    induction i with
    | zero => simpa using base
    | succ i ih =>
      have lt : i<11 := by omega
      obtain ⟨c,s⟩ := ih (by omega)
      let u := (2:ℝ)^i*a
      have cu := (Rat.cast_le (K:=ℝ)).mpr (T.unitC i lt.le)
      have su := (Rat.cast_le (K:=ℝ)).mpr (T.unitS i lt.le)
      have rc := (Rat.cast_le (K:=ℝ)).mpr (T.cosStep i lt)
      have rs := (Rat.cast_le (K:=ℝ)).mpr (T.sinStep i lt)
      push_cast at cu su rc rs
      rw [abs_sub_comm] at rc rs
      have cc := product_error (Real.abs_cos_le_one u) cu c c
      have ss := product_error (Real.abs_sin_le_one u) su s s
      have sc := product_error (Real.abs_sin_le_one u) cu s c
      have e : err (i+1)=4*err i+1/10^14 := by dsimp [err]; rw [pow_succ]; ring
      have angle : (2:ℝ)^(i+1)*a=2*u := by dsimp [u]; rw [pow_succ]; ring
      rw [angle,e,Real.sin_two_mul,Real.cos_two_mul']
      constructor
      · have dif : |Real.cos u^2-Real.sin u^2-((T.C i:ℝ)^2-(T.S i:ℝ)^2)|≤4*err i := by
          rw [show Real.cos u^2-Real.sin u^2-((T.C i:ℝ)^2-(T.S i:ℝ)^2)=
              (Real.cos u*Real.cos u-(T.C i:ℝ)*(T.C i:ℝ))-(Real.sin u*Real.sin u-(T.S i:ℝ)*(T.S i:ℝ)) by ring]
          exact (abs_sub _ _).trans (by linarith)
        exact (abs_sub_le _ ((T.C i:ℝ)^2-(T.S i:ℝ)^2) _).trans (by linarith)
      · have dif : |2*Real.sin u*Real.cos u-2*(T.S i:ℝ)*(T.C i:ℝ)|≤4*err i := by
          rw [show 2*Real.sin u*Real.cos u-2*(T.S i:ℝ)*(T.C i:ℝ)=
            2*(Real.sin u*Real.cos u-(T.S i:ℝ)*(T.C i:ℝ)) by ring,abs_mul]
          norm_num
          linarith
        exact (abs_sub_le _ (2*(T.S i:ℝ)*(T.C i:ℝ)) _).trans (by linarith)
  have hh := all 11 (by decide)
  have last : (2:ℝ)^11*a=(q:ℝ) := by dsimp [a]; ring
  rw [last] at hh
  exact ⟨hh.1.trans (by norm_num [err]),hh.2.trans (by norm_num [err])⟩

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.double_angles_sound
