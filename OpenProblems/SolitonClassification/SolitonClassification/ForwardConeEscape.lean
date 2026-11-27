import SolitonClassification.PeriodicConeRigidity

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation.Cone
open Set

private theorem no_bounded_positive_steps (P : ℕ → Prop) (score : ℕ → ℝ)
    {g B : ℝ} (gp : 0<g) (bounded : ∀ n,score n≤B)
    (step : ∀ n,P n → P (n+1) ∧ score n+g≤score (n+1)) : ∀ n, ¬P n := by
  intro n hn
  have h (k : ℕ) : P (n+k) ∧ score n+k*g≤score (n+k) := by
    induction k with
    | zero => simpa using hn
    | succ k ih =>
      obtain ⟨ok,inc⟩ := step (n+k) ih.1
      refine ⟨ok,?_⟩
      rw [Nat.cast_succ]
      rw [Nat.add_assoc] at inc
      linarith [ih.2]
  obtain ⟨k,hk⟩ := exists_nat_gt ((B-score n)/g)
  exact (not_lt_of_ge ((h k).2.trans (bounded _)))
    (by linarith [(div_lt_iff₀ gp).mp hk])

/-- Bounded forward orbits of the local two-point inequalities have
    arbitrarily small displacement. Compact forward trapping consequently
    requires a fixed point in the trapping set, even for an aperiodic orbit. -/
theorem bounded_orbits_have_small_steps (x : ℕ → Section) (R : ℝ) (bounded : ∀ n, ‖x n‖≤R)
    (a u e : ℝ) (ep : 0≤e) (stable : |a|+2*e<1) (unstable : 1+2*e< |u|)
    (err : let v := fun n => x (n+1)-x n
      ∀ n, |v (n+1) 0-a*v n 0|≤e*‖v n‖ ∧ |v (n+1) 1-v n 1|≤e*‖v n‖ ∧
        |v (n+1) 2-u*v n 2|≤e*‖v n‖) :
    ∀ g>0, ∃ n, ‖x (n+1)-x n‖<g := by
  intro g gp
  by_contra! lower
  let v := fun n => x (n+1)-x n
  let m := fun n => ‖v n‖
  let U := fun n => |v n 2|=m n
  let S := fun n => |v n 0|=m n
  have cb (n : ℕ) (j : Fin 3) : |v n j|≤m n := norm_le_pi_norm (v n) j
  have mb (n : ℕ) : m n ≤ 2*R := by
    have est := norm_sub_le (x (n+1)) (x n)
    linarith only [est,bounded (n+1),bounded n]
  have mp (n : ℕ) : 0<m n := gp.trans_le (lower n)
  have top (n : ℕ) : S n ∨ |v n 1|=m n ∨ U n := by
    by_contra! no
    obtain ⟨s,c,u⟩ := no
    have strict (i : Fin 3) : ‖v n i‖<m n := by
      fin_cases i
      · exact lt_of_le_of_ne (cb n 0) s
      · exact lt_of_le_of_ne (cb n 1) c
      · exact lt_of_le_of_ne (cb n 2) u
    exact (lt_irrefl (m n)) ((pi_norm_lt_iff (mp n)).mpr strict)
  have triangle {A B r : ℝ} (h : |A-B|≤r) : |A|≤ |B|+r ∧ |B|≤ |A|+r := by
    have h1 := abs_add_le (A-B) B
    have h2 := abs_add_le (B-A) A
    rw [sub_add_cancel] at h1 h2
    rw [abs_sub_comm B A] at h2
    constructor <;> linarith
  have hS (n : ℕ) : |v (n+1) 0|≤(|a|+e)*m n := by
    have h := (triangle (err n).1).1
    rw [abs_mul] at h
    change |v (n+1) 0|≤ |a| * |v n 0|+e*m n at h
    nlinarith only [h,mul_le_mul_of_nonneg_left (cb n 0) (abs_nonneg a)]
  have hC (n : ℕ) : |v (n+1) 1|≤(1+e)*m n := by
    have h : |v (n+1) 1|≤ |v n 1|+e*m n := (triangle (err n).2.1).1
    linarith [cb n 1]
  have notU : ∀ n, ¬ U n := by
    apply no_bounded_positive_steps U m (g:=(|u|-e-1)*g) (B:=2*R) (mul_pos (by linarith) gp) mb
    intro n dom
    have h := (triangle (err n).2.2).2
    rw [abs_mul] at h
    change |u| * |v n 2|≤ |v (n+1) 2|+e*m n at h
    rw [dom] at h
    have big : (1+e)*m n< |v (n+1) 2| := by nlinarith only [mul_lt_mul_of_pos_right unstable (mp n),h]
    have st : |v (n+1) 0|< |v (n+1) 2| := by
      nlinarith only [hS n,mul_le_mul_of_nonneg_right (show |a|≤1 by linarith) (mp n).le,big]
    have un : U (n+1) := (top (n+1)).resolve_left
      (fun eq => by rw [eq] at st; exact st.not_ge (cb _ 2)) |>.resolve_left
        (fun eq => by have hc := (hC n).trans_lt big; rw [eq] at hc; exact hc.not_ge (cb _ 2))
    refine ⟨un,?_⟩
    rw [←un]
    nlinarith only [h,mul_le_mul_of_nonneg_left (show g≤m n from lower n) (show 0≤ |u|-e-1 by linarith)]
  have prev (n : ℕ) (sn : S (n+1)) : S n ∧ m (n+1)+(1-|a|-e)*g≤m n := by
    have s := hS n
    rw [sn] at s
    have eq : S n := by
      rcases top n with dom | eq | dom
      · exact dom
      · have h : |v n 1|≤ |v (n+1) 1|+e*m n := (triangle (err n).2.1).2
        rw [eq] at h
        nlinarith only [h,cb (n+1) 1,s,mul_lt_mul_of_pos_right stable (mp n)]
      · exact (notU n dom).elim
    refine ⟨eq,?_⟩
    nlinarith only [s,mul_le_mul_of_nonneg_left (show g≤m n from lower n) (show 0≤1-|a|-e by linarith)]
  obtain ⟨N,off⟩ : ∃ N, ¬ S N := by
    by_contra! all
    have no := no_bounded_positive_steps (fun _ => True) (fun n => -m n)
      (g:=(1-|a|-e)*g) (B:=0) (mul_pos (by linarith) gp)
      (fun n => neg_nonpos.mpr (mp n).le) (fun n _ => ⟨trivial,by linarith [(prev n (all _)).2]⟩)
    exact no 0 trivial
  have tail (k : ℕ) : ¬ S (N+k) := by
    induction k with
    | zero => simpa using off
    | succ k ih => exact fun h => ih (prev (N+k) h).1
  have centre (k : ℕ) : |v (N+k) 1|=m (N+k) :=
    ((top _).resolve_left (tail k)).resolve_right (notU _)
  have small : e<1 := by linarith [abs_nonneg a]
  have xb (k : ℕ) : |x (N+k) 1|≤R := (norm_le_pi_norm _ _).trans (bounded _)
  have noPlus := no_bounded_positive_steps (fun k => 0<v (N+k) 1) (fun k => x (N+k) 1)
    gp (fun k => (le_abs_self _).trans (xb k)) (fun k pos => by
      have h : |v (N+(k+1)) 1-v (N+k) 1|≤e*m (N+k) := (err _).2.1
      have eq := centre k
      rw [abs_of_pos pos] at eq
      refine ⟨by nlinarith only [(abs_le.mp h).1,eq,mul_lt_mul_of_pos_right small (mp (N+k))],?_⟩
      have hh : g≤x (N+(k+1)) 1-x (N+k) 1 := (lower _).trans eq.ge
      linarith)
  have noMinus := no_bounded_positive_steps (fun k => v (N+k) 1<0) (fun k => -x (N+k) 1)
    gp (fun k => (neg_le_abs _).trans (xb k)) (fun k neg => by
      have h : |v (N+(k+1)) 1-v (N+k) 1|≤e*m (N+k) := (err _).2.1
      have eq := centre k
      rw [abs_of_neg neg] at eq
      refine ⟨by nlinarith only [(abs_le.mp h).2,eq,mul_lt_mul_of_pos_right small (mp (N+k))],?_⟩
      have hh : g≤-(x (N+(k+1)) 1-x (N+k) 1) := (lower _).trans eq.ge
      linarith)
  have zero : v (N+0) 1=0 := le_antisymm (not_lt.mp (noPlus 0)) (not_lt.mp (noMinus 0))
  have eq := centre 0
  rw [zero,abs_zero] at eq
  exact (mp _).ne eq

end ClosedSimilarity.RotatingBifurcation.Cone
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.bounded_orbits_have_small_steps
