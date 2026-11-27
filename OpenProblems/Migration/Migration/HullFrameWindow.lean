import Migration.HullCriticalWindow
import Migration.HullStressWindow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set Metric
namespace MigrationGeometry.HullGap
open Adjoint
set_option maxHeartbeats 600000

def frameState {L : ℝ} (f : Frame 1 L) (s : ℝ) : State :=
  ![f.k s,f.v s,f.p s,f.q s,f.h s,f.u s,f.n s,f.primitive A s]
def primitiveValue (z : State) :=
  weight z*(z 3*z 4-((z 0)^2/2*z 5+z 1*z 6))+
    z 3*z 0*z 6-(1+z 0*z 2)*z 5+(z 1*z 2+(z 0)^2/2*z 3)*z 4

theorem frameState_d {L : ℝ} (f : Frame 1 L) (s : ℝ) :
    HasDerivAt (frameState f) (velocity (frameState f s)) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact f.kD s
  · simpa [velocity,frameState] using f.vD s
  · exact f.pD s
  · exact f.qD s
  · exact f.hD s
  · exact f.uD s
  · exact f.nD s
  · simpa [velocity,frameState,density,weight,Frame.density,Frame.weight] using f.primitiveD A s

theorem frameState_periodic {L : ℝ} (f : Frame 1 L) : Function.Periodic (frameState f) L := by
  intro s
  obtain ⟨k,v,p,q,h,u,n⟩ := f.periodic s
  simp [frameState,Frame.primitive,Frame.weight,Frame.stress,Frame.virial,k,v,p,q,h,u,n]

theorem velocity_smooth : ContDiff ℝ 1 velocity := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [velocity,density,weight] <;> fun_prop

private theorem eight_bound (x0 x1 x2 x3 x4 x5 x6 x7 K : ℝ) (kp : 0≤K)
    (a : |x0|≤K) (b : |x1|≤K) (c : |x2|≤K) (d : |x3|≤K)
    (e : |x4|≤K) (f : |x5|≤K) (g : |x6|≤K) (h : |x7|≤K) :
    ‖(![x0,x1,x2,x3,x4,x5,x6,x7] : State)‖≤K := by
  apply (pi_norm_le_iff_of_nonneg kp).mpr
  intro i
  fin_cases i
  · exact a
  · exact b
  · exact c
  · exact d
  · exact e
  · exact f
  · exact g
  · exact h

private theorem frame_bounds {L : ℝ} (f : Frame 1 L) (s : ℝ)
    (rad : ∀ s, (f.p s)^2+(f.q s)^2≤4) (unit : ∀ s, (f.u s)^2+(f.n s)^2=1) :
    |f.k s|≤1000 ∧ |f.v s|≤1000 ∧ |f.p s|≤2 ∧ |f.q s|≤2 ∧ |f.h s|≤4 ∧ |f.u s|≤1 ∧ |f.n s|≤1 := by
  have vcap := f.stressSize_disk_two rad s
  obtain ⟨vv,kk⟩ := f.stressSize_dominates s
  have k : |f.k s|≤1000 := by
    rw [← abs_of_pos (by norm_num : (0:ℝ)<1000)]
    apply sq_le_sq.mp; linarith only [kk,vcap]
  have p : |f.p s|≤2 := by
    rw [← abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply sq_le_sq.mp; linarith only [rad s,sq_nonneg (f.q s)]
  have q : |f.q s|≤2 := by
    rw [← abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply sq_le_sq.mp; linarith only [rad s,sq_nonneg (f.p s)]
  have u : |f.u s|≤1 := by
    simpa using sq_le_sq.mp (show (f.u s)^2≤(1:ℝ)^2 by linarith only [unit s,sq_nonneg (f.n s)])
  have n : |f.n s|≤1 := by
    simpa using sq_le_sq.mp (show (f.n s)^2≤(1:ℝ)^2 by linarith only [unit s,sq_nonneg (f.u s)])
  have h : |f.h s|≤4 := by
    rw [f.decompose s]
    refine (abs_add_le ..).trans ?_
    simp only [abs_mul]
    linarith only [mul_le_mul q u (abs_nonneg _) (by norm_num : (0:ℝ)≤2),
      mul_le_mul p n (abs_nonneg _) (by norm_num : (0:ℝ)≤2)]
  exact ⟨k,vv.trans vcap.le,p,q,h,u,n⟩

private theorem plus_bound {a b C D : ℝ} (x : |a|≤C) (y : |b|≤D) : |a+b|≤C+D :=
  (abs_add_le ..).trans (add_le_add x y)
private theorem minus_bound {a b C D : ℝ} (x : |a|≤C) (y : |b|≤D) : |a-b|≤C+D := by
  simpa [sub_eq_add_neg] using plus_bound x (show |-b|≤D by simpa using y)
private theorem times_bound {a b C D : ℝ} (x : |a|≤C) (y : |b|≤D) : |a*b|≤C*D := by
  rw [abs_mul]
  exact mul_le_mul x y (abs_nonneg _) ((abs_nonneg _).trans x)

theorem uniform_frame_bound : ∃ K : ℝ, ∀ {L : ℝ} (f : Frame 1 L),
    (∀ s, (f.p s)^2+(f.q s)^2≤4) →
    (∀ s, (f.u s)^2+(f.n s)^2=1) → ∀ s, ‖frameState f s‖≤K := by
  refine ⟨100000000,fun {L} f rad unit s => ?_⟩
  obtain ⟨k,v,p,q,h,u,n⟩ := frame_bounds f s rad unit
  have U : |f.k s^2/2|≤500000 := by
    rw [abs_div,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have po := pow_le_pow_left₀ (abs_nonneg _) k 2
    linarith
  have weight_bound : |f.weight A s|≤4 := by
    unfold Frame.weight
    rw [abs_of_nonneg (by positivity)]
    have lim : A^2≤4 := by rw [A_sq]; exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    linarith only [lim,rad s]
  have vir := plus_bound (times_bound v p) (times_bound U q)
  have stress := plus_bound (times_bound U u) (times_bound v n)
  have first := times_bound weight_bound (minus_bound (times_bound q h) stress)
  have second := times_bound (times_bound q k) n
  have third := times_bound (plus_bound (show |(1:ℝ)|≤1 by norm_num) (times_bound k p)) u
  have all := plus_bound (minus_bound (plus_bound first second) third) (times_bound vir h)
  have prim : |f.primitive A s| ≤ 100000000 := by
    simpa only [Frame.primitive,Frame.stress,Frame.virial,one_mul] using
      all.trans (by norm_num)
  exact eight_bound _ _ _ _ _ _ _ _ _ (by norm_num) (k.trans (by norm_num))
    (v.trans (by norm_num)) (p.trans (by norm_num)) (q.trans (by norm_num))
    (h.trans (by norm_num)) (u.trans (by norm_num)) (n.trans (by norm_num)) prim

end MigrationGeometry.HullGap
#print axioms MigrationGeometry.HullGap.uniform_frame_bound
