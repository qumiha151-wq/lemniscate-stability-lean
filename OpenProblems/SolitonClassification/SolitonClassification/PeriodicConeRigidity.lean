import SolitonClassification.OddLocalRigidity
import Mathlib.Tactic.FinCases

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation.Cone
open Filter Set Topology

abbrev Section := Fin 3 → ℝ

private theorem no_escape {I : Type*} [Finite I] (next : I → I) (score : I → ℝ)
    (P : I → Prop) (rise : ∀ i, P i → P (next i) ∧ score i < score (next i)) :
    ∀ i, ¬ P i := by
  classical
  let _ := Fintype.ofFinite I
  intro i hi
  let fs := Finset.univ.filter P
  have nonempty : fs.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨j,hj,largest⟩ := Finset.exists_max_image fs score nonempty
  obtain ⟨ok,bigger⟩ := rise j (Finset.mem_filter.mp hj).2
  exact bigger.not_ge (largest _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok⟩))

private def size (x : Section) := max |x 0| (max |x 1| |x 2|)

private theorem coord_bound (x : Section) (j : Fin 3) : |x j|≤size x := by
  fin_cases j
  · exact le_max_left .. 
  · exact (le_max_left ..).trans (le_max_right ..)
  · exact (le_max_right ..).trans (le_max_right ..)

private theorem norm_eq_size (x : Section) : ‖x‖=size x := by
  have nonneg : 0≤size x := (abs_nonneg _).trans (coord_bound x 0)
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg nonneg).mpr fun j => (coord_bound x j)
  · exact max_le (norm_le_pi_norm x 0)
      (max_le (norm_le_pi_norm x 1) (norm_le_pi_norm x 2))

private theorem bounds {x y m : ℝ} (e : |x-y|≤m) :
    |x|≤ |y|+m ∧ |y|≤ |x|+m := by
  have h1 := abs_add_le (x-y) y
  have h2 := abs_add_le (y-x) x
  rw [sub_add_cancel] at h1 h2
  rw [abs_sub_comm y x] at h2
  constructor <;> linarith

/-- In stable, neutral and unstable coordinates, all finite cycles are fixed
    if the error between any two successive step vectors is small compared
    with their maximum coordinate. No bound on the cycle length is imposed. -/
theorem finite_cycles_fixed {I : Type*} [Finite I] (next : Equiv.Perm I) (x : I → Section)
    (a u e : ℝ) (ep : 0≤e) (stable : |a|+2*e<1) (unstable : 1+2*e< |u|)
    (err : let v := fun i => x (next i)-x i
      ∀ i, |v (next i) 0-a*v i 0|≤e*‖v i‖ ∧
        |v (next i) 1-v i 1|≤e*‖v i‖ ∧ |v (next i) 2-u*v i 2|≤e*‖v i‖) :
    ∀ i, x (next i)=x i := by
  simp_rw [norm_eq_size] at err
  let v := fun i => x (next i)-x i
  let m := fun i => size (v i)
  let U := fun i => 0<m i ∧ |v i 2|=m i
  let S := fun i => 0<m i ∧ |v i 0|=m i
  have bound (i : I) (j : Fin 3) : |v i j|≤m i := coord_bound (v i) j
  have h0 (i : I) : |v (next i) 0| ≤ |a| * |v i 0|+e*m i := by
    simpa only [abs_mul] using (bounds (err i).1).1
  have h1 (i : I) := bounds (err i).2.1
  have h2 (i : I) : |u| * |v i 2| ≤ |v (next i) 2|+e*m i := by
    simpa only [abs_mul] using (bounds (err i).2.2).2
  have hS (i : I) : |v (next i) 0| ≤ (|a|+e)*m i := by
    nlinarith only [h0 i,mul_le_mul_of_nonneg_left (bound i 0) (abs_nonneg a)]
  have hC (i : I) : |v (next i) 1| ≤ (1+e)*m i := by
    have e1 : |v (next i) 1| ≤ |v i 1|+e*m i := (h1 i).1
    linarith [bound i 1]
  have notU : ∀ i, ¬ U i := by
    apply no_escape next m U
    intro i hi
    have hu := h2 i
    rw [hi.2] at hu
    have big : (1+e)*m i< |v (next i) 2| := by
      nlinarith only [mul_lt_mul_of_pos_right unstable hi.1,hu]
    have s := hS i
    have ab : |a|≤1 := by linarith
    have rs : |v (next i) 0|≤ |v (next i) 2| := by
      nlinarith only [s,big,mul_le_mul_of_nonneg_right ab hi.1.le]
    have eq : m (next i)=|v (next i) 2| :=
      by simp only [m,size,max_eq_right ((hC i).trans big.le),max_eq_right rs]
    have grow : m i < m (next i) := by
      rw [eq]
      nlinarith only [big,mul_nonneg ep hi.1.le]
    exact ⟨⟨hi.1.trans grow,eq.symm⟩,grow⟩
  have notS : ∀ i, ¬ S i := by
    apply no_escape next.symm m S
    intro j hj
    let i := next.symm j
    have ni : next i=j := next.apply_symm_apply _
    have s := hS i
    rw [ni,hj.2] at s
    have mi : 0<m i := by
      by_contra! zero
      have k := mul_nonpos_of_nonneg_of_nonpos (add_nonneg (abs_nonneg a) ep) zero
      linarith [hj.1]
    have less : m j<m i := by
      nlinarith only [s,mul_lt_mul_of_pos_right stable mi,mul_nonneg ep mi.le]
    refine ⟨⟨mi,?_⟩,less⟩
    by_contra diff
    have cu : |v i 2|≠m i := fun eq => notU i ⟨mi,eq⟩
    have mid : |v i 1|=m i := by
      by_contra d
      have b0 := lt_of_le_of_ne (bound i 0) diff
      have b1 := lt_of_le_of_ne (bound i 1) d
      have b2 := lt_of_le_of_ne (bound i 2) cu
      exact (lt_irrefl (m i)) (max_lt b0 (max_lt b1 b2))
    have reverse : |v i 1|≤ |v (next i) 1|+e*m i := (h1 i).2
    rw [mid,ni] at reverse
    nlinarith only [reverse,bound j 1,s,mul_lt_mul_of_pos_right stable mi]
  have centre (i : I) : |v i 1|=m i := by
    by_contra d
    have pos : 0<m i := (abs_nonneg _).trans_lt (lt_of_le_of_ne (bound i 1) d)
    have b0 := lt_of_le_of_ne (bound i 0) (fun eq => notS i ⟨pos,eq⟩)
    have b1 := lt_of_le_of_ne (bound i 1) d
    have b2 := lt_of_le_of_ne (bound i 2) (fun eq => notU i ⟨pos,eq⟩)
    exact (lt_irrefl (m i)) (max_lt b0 (max_lt b1 b2))
  have small : e<1 := by linarith [abs_nonneg a]
  have plus : ∀ i, ¬ 0<v i 1 := by
    apply no_escape next (fun i => x i 1) (fun i => 0<v i 1)
    intro i hi
    have h : |v (next i) 1-v i 1|≤e*m i := (err i).2.1
    rw [←centre i,abs_of_pos hi] at h
    exact ⟨by nlinarith only [(abs_le.mp h).1,mul_lt_mul_of_pos_right small hi],sub_pos.mp hi⟩
  have minus : ∀ i, ¬ v i 1<0 := by
    apply no_escape next (fun i => -x i 1) (fun i => v i 1<0)
    intro i hi
    have h : |v (next i) 1-v i 1|≤e*m i := (err i).2.1
    rw [←centre i,abs_of_neg hi] at h
    exact ⟨by nlinarith only [(abs_le.mp h).2,mul_lt_mul_of_pos_right small (neg_pos.mpr hi)],
      neg_lt_neg (sub_neg.mp hi)⟩
  intro i
  have zero : v i 1=0 := le_antisymm (not_lt.mp (plus i)) (not_lt.mp (minus i))
  have z : m i=0 := by rw [←centre i,zero,abs_zero]
  apply sub_eq_zero.mp
  funext j
  exact abs_nonpos_iff.mp ((bound i j).trans_eq z)

end ClosedSimilarity.RotatingBifurcation.Cone
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.finite_cycles_fixed
