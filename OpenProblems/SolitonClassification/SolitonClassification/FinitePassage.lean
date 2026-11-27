import SolitonClassification.PeriodicConeRigidity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation.Cone

/-- A bounded scalar function that pays for each section displacement.
    Its offsets distinguish the three possible stages of a finite passage. -/
private def account (D : ℝ) (x v : Section) :=
  if |v 2|=‖v‖ then 6*D+‖v‖
  else if |v 0|=‖v‖ then -‖v‖
  else if 0≤v 1 then 3*D+x 1 else 3*D-x 1

private theorem account_bounds {D : ℝ} {x v : Section} (dp : 0≤D)
    (xc : |x 1|≤D) (vc : ‖v‖≤2*D) :
    -2*D≤account D x v ∧ account D x v≤8*D := by
  unfold account
  split_ifs <;> constructor <;> linarith [norm_nonneg v,(abs_le.mp xc).1,(abs_le.mp xc).2]

private theorem error_triangle {a b r : ℝ} (h : |a-b|≤r) : |a|≤|b|+r ∧ |b|≤|a|+r := by
  have l := abs_add_le (a-b) b
  have t := abs_add_le (b-a) a
  rw [sub_add_cancel] at l t
  rw [abs_sub_comm b a] at t
  constructor <;> linarith

private theorem centre_wins (v : Section) (s : |v 0|≠‖v‖) (u : |v 2|≠‖v‖) :
    |v 1|=‖v‖ := by
  by_contra c
  have p : 0<‖v‖ := (abs_nonneg _).trans_lt (lt_of_le_of_ne (norm_le_pi_norm v 1) c)
  apply (lt_irrefl ‖v‖)
  apply (pi_norm_lt_iff p).mpr
  intro j
  fin_cases j
  · exact lt_of_le_of_ne (norm_le_pi_norm v 0) s
  · exact lt_of_le_of_ne (norm_le_pi_norm v 1) c
  · exact lt_of_le_of_ne (norm_le_pi_norm v 2) u

private theorem pay_step (D a u e c : ℝ) (cp : 0<c) (c1 : c≤1)
    (ep : 0≤e) (hS : c≤1-|a|-e) (hU : c≤|u|-e-1)
    (gapS : |a|+2*e<1) (gapU : 1+2*e< |u|)
    (x y v w : Section) (xy : y 1=x 1+v 1) (xd : |x 1|≤D) (yd : |y 1|≤D)
    (vd : ‖v‖≤2*D) (h0 : |w 0-a*v 0|≤e*‖v‖)
    (h1 : |w 1-v 1|≤e*‖v‖) (h2 : |w 2-u*v 2|≤e*‖v‖) :
    account D x v+c*‖v‖≤account D y w := by
  have dp := (abs_nonneg _).trans xd
  have vm := norm_nonneg v
  have cm := (mul_le_mul_of_nonneg_right c1 vm).trans_eq (one_mul _)
  have A : |w 0|≤(|a|+e)*‖v‖ := by
    have h := (error_triangle h0).1
    rw [abs_mul] at h
    rw [add_mul]
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (abs_nonneg a)) le_rfl)
  have B : |w 1|≤(1+e)*‖v‖ := by
    have h := (error_triangle h1).1
    linarith [show |v 1|≤‖v‖ from norm_le_pi_norm v 1]
  have C : |u| * |v 2|≤|w 2|+e*‖v‖ := by simpa only [abs_mul] using (error_triangle h2).2
  by_cases U : |v 2|=‖v‖
  · rw [U] at C
    by_cases zero : ‖v‖=0
    · have z := norm_eq_zero.mp zero
      subst v
      have w0 : w=0 := by
        have p0 : |w 0|≤0 := by simpa using h0
        have p1 : |w 1|≤0 := by simpa using h1
        have p2 : |w 2|≤0 := by simpa using h2
        ext j
        fin_cases j
        · exact abs_nonpos_iff.mp p0
        · exact abs_nonpos_iff.mp p1
        · exact abs_nonpos_iff.mp p2
      rw [w0]
      simp [account]
    have vp := lt_of_le_of_ne vm (Ne.symm zero)
    have big : (1+e)*‖v‖< |w 2| := by nlinarith only [mul_lt_mul_of_pos_right gapU vp,C]
    have win : |w 2|=‖w‖ := by
      by_contra not
      have zs : |w 0|≠‖w‖ := by
        intro eq
        rw [eq] at A
        have bu : |w 2|≤‖w‖ := norm_le_pi_norm w 2
        nlinarith only [A,bu,big,mul_le_mul_of_nonneg_right (show |a|≤1 by linarith) vm]
      exact (B.trans_lt big).not_ge ((norm_le_pi_norm w 2 : |w 2|≤‖w‖).trans_eq (centre_wins w zs not).symm)
    simp only [account,if_pos U,if_pos win]
    rw [←win]
    nlinarith only [C,mul_le_mul_of_nonneg_right hU vm]
  by_cases W : |w 2|=‖w‖
  · simp only [account,if_neg U,if_pos W]
    split_ifs <;> linarith [norm_nonneg w,(abs_le.mp xd).1,(abs_le.mp xd).2]
  by_cases S : |v 0|=‖v‖
  · simp only [account,if_neg U,if_neg W,if_pos S]
    split_ifs with ws sign
    · rw [ws] at A
      nlinarith only [A,mul_le_mul_of_nonneg_right hS vm]
    · linarith [(abs_le.mp yd).1]
    · linarith [(abs_le.mp yd).2]
  have eq := centre_wins v S U
  have vp : 0<‖v‖ := (abs_nonneg _).trans_lt (lt_of_le_of_ne (norm_le_pi_norm v 2) U)
  have NS : |w 0|≠‖w‖ := by
    intro ws
    rw [ws] at A
    have r := (error_triangle h1).2
    rw [eq] at r
    nlinarith only [r,show |w 1|≤‖w‖ from norm_le_pi_norm w 1,A,mul_lt_mul_of_pos_right gapS vp]
  simp only [account,if_neg U,if_neg S,if_neg W,if_neg NS]
  have sm : e<1 := by linarith [abs_nonneg a]
  by_cases positive : 0≤v 1
  · rw [abs_of_nonneg positive] at eq
    have after : 0≤w 1 := by nlinarith only [(abs_le.mp h1).1,eq,mul_lt_mul_of_pos_right sm vp]
    rw [if_pos positive,if_pos after]
    linarith
  · rw [abs_of_neg (lt_of_not_ge positive)] at eq
    have after : ¬0≤w 1 := by nlinarith only [(abs_le.mp h1).2,eq,mul_lt_mul_of_pos_right sm vp]
    rw [if_neg positive,if_neg after]
    linarith

/-- Uniform bound on the total section displacement over every finite
    passage. The constant depends on the spectral gaps and the chart radius.
    It is independent of the number of returns. -/
theorem finite_passage_variation (a u e : ℝ) (ep : 0≤e)
    (hs : |a|+2*e<1) (hu : 1+2*e< |u|) :
    ∃ c>0, ∀ (x : ℕ → Section) (N : ℕ) (D : ℝ),
      (∀ n≤N+1, ‖x n‖≤D) →
      (let v := fun n => x (n+1)-x n
       ∀ n<N, |v (n+1) 0-a*v n 0|≤e*‖v n‖ ∧ |v (n+1) 1-v n 1|≤e*‖v n‖ ∧
         |v (n+1) 2-u*v n 2|≤e*‖v n‖) →
      c*(∑ n∈Finset.range N, ‖x (n+1)-x n‖)≤10*D := by
  let c := min 1 (min (1-|a|-e) (|u|-e-1))
  have cp : 0<c := lt_min zero_lt_one (lt_min (by linarith) (by linarith))
  refine ⟨c,cp,?_⟩
  intro x N D inside err
  let v := fun n => x (n+1)-x n
  let f := fun n => account D (x n) (v n)
  have vx (n : ℕ) (h : n≤N+1) : |x n 1|≤D := (norm_le_pi_norm _ _).trans (inside n h)
  have vn (n : ℕ) (h : n≤N) : ‖v n‖≤2*D := by
    have t := norm_sub_le (x (n+1)) (x n)
    change ‖x (n+1)-x n‖≤2*D
    linarith [inside (n+1) (by omega),inside n (by omega)]
  have dp : 0≤D := (norm_nonneg _).trans (inside 0 (Nat.zero_le _))
  have step (n : ℕ) (h : n<N) : f n+c*‖v n‖≤f (n+1) := by
    apply pay_step D a u e c cp (min_le_left ..) ep ((min_le_right ..).trans (min_le_left ..))
      ((min_le_right ..).trans (min_le_right ..)) hs hu (x n) (x (n+1)) (v n) (v (n+1))
    · dsimp [v]; ring
    · exact vx n (by omega)
    · exact vx (n+1) (by omega)
    · exact vn n h.le
    · exact (err n h).1
    · exact (err n h).2.1
    · exact (err n h).2.2
  have total (k : ℕ) (hk : k≤N) :
      f 0+c*(∑ n∈Finset.range k, ‖v n‖)≤f k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ,mul_add]
      linarith [step k hk,ih (Nat.le_of_succ_le hk)]
  have low := (account_bounds dp (vx 0 (by omega)) (vn 0 (by omega))).1
  have high := (account_bounds dp (vx N (by omega)) (vn N le_rfl)).2
  change -2*D≤f 0 at low
  change f N≤8*D at high
  change c*(∑ n∈Finset.range N, ‖v n‖)≤10*D
  linarith [total N le_rfl]

end ClosedSimilarity.RotatingBifurcation.Cone
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.finite_passage_variation
