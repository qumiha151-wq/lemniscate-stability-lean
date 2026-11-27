import SolitonClassification.Rotating.IntegerGeometricShooting
import SolitonClassification.Rotating.ResetShootingFamily
import SolitonClassification.Rotating.ResetShortTail

/-! The selected two-sided flow equals the true cell trajectories on either
signed tape. The first five coordinates of the cutoff are bounded by ten.
The tangent angle is unrestricted. -/
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric DyadicReset
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def wideClip (a : State) : State :=
  fun i => if i=5 then a i else clipScalar 10 (a i)

theorem wideClip_box (a : State) : StateBox (wideClip a) := by
  intro i hi
  have ne : i≠5 := by omega
  simp only [wideClip,if_neg ne]
  exact clipScalar_bound (by norm_num) _

theorem wideClip_id {a : State} (ha : StateBox a) : wideClip a=a := by
  ext i
  by_cases hi : i=5
  · simp [wideClip,hi]
  · simp only [wideClip,if_neg hi]
    exact clipScalar_eq_self (ha i (by omega))

theorem wideClip_lipschitz : LipschitzWith 1 wideClip := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro a b
  simp only [NNReal.coe_one,one_mul]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have hd := coordinate_bound (a-b) i
  change |a i-b i|≤_ at hd
  simp only [Pi.sub_apply,Real.norm_eq_abs,wideClip]
  by_cases h : i=5
  · simpa only [if_pos h] using hd
  · simp only [if_neg h]
    have hc := (clipScalar_lipschitz 10).dist_le_mul (a i) (b i)
    exact (show |clipScalar 10 (a i)-clipScalar 10 (b i)|≤|a i-b i| from
      by simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using hc).trans hd

def wideField (a : State) : State := field (wideClip a)
theorem wideField_lipschitz : LipschitzWith 40 wideField := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro a b
  have h := field_wide_lip (wideClip_box a) (wideClip_box b)
  have k := (lipschitzWith_iff_norm_sub_le.mp wideClip_lipschitz) a b
  simp only [NNReal.coe_one,one_mul] at k
  exact h.trans (mul_le_mul_of_nonneg_left k (by norm_num))

theorem wideField_bound (a : State) : ‖wideField a‖≤(110:ℝ≥0) :=
  true_speed (wideClip_box a)

def wideFlow (u : ℝ×State) : State :=
  (exists_unique_global_bounded_flow wideField_lipschitz wideField_bound u.2).exists.choose u.1
theorem wideFlow_zero (a : State) : wideFlow (0,a)=a :=
  (exists_unique_global_bounded_flow wideField_lipschitz wideField_bound a).exists.choose_spec.1
theorem wideFlow_time (a : State) (s : ℝ) :
    HasDerivAt (fun t => wideFlow (t,a)) (wideField (wideFlow (s,a))) s :=
  (exists_unique_global_bounded_flow wideField_lipschitz wideField_bound a).exists.choose_spec.2 s

theorem cell_identification {s l : ℝ} (hs : |s|≤1/100) (a : State) {x : ℝ→State}
    (ini : x 0=wideFlow (l,a)) (dx : FollowsState s x)
    (box : ∀t∈unitCell, StateBox (x t)) :
    ∀t∈unitCell, x t=wideFlow (l+t*s,a) := by
  let y := fun t : ℝ => wideFlow (l+t*s,a)
  have dy (t : ℝ) : HasDerivAt y (s • wideField (y t)) t := by
    have d := ((hasDerivAt_id t).mul_const s).const_add l
    simpa only [y,Function.comp_def,id_eq,one_mul] using (wideFlow_time a (l+t*s)).scomp t d
  let e := fun t => x t-y t
  let v := fun t => s • (wideField (x t)-wideField (y t))
  have de (t : ℝ) (ht : t∈unitCell) : HasDerivWithinAt e (v t) unitCell t := by
    have dex := (dx t ht).sub (dy t).hasDerivWithinAt
    dsimp only [v]
    rw [smul_sub,show wideField (x t)=field (x t) by rw [wideField,wideClip_id (box t ht)]]
    simpa only [e,Pi.sub_def] using dex
  have hb (t : ℝ) (_ : t∈unitCell) : ‖v t‖≤(2/5)*‖e t‖+0 := by
    have h := lipschitzWith_iff_norm_sub_le.mp wideField_lipschitz (x t) (y t)
    rw [show ‖v t‖=|s| * ‖wideField (x t)-wideField (y t)‖ by simp [v,norm_smul,Real.norm_eq_abs]]
    have m := mul_le_mul hs h (norm_nonneg _) (by norm_num : 0≤(1:ℝ)/100)
    dsimp only [e]
    exact m.trans_eq (by norm_num; ring)
  have zero : e 0=0 := by simp [e,y,ini]
  intro t ht
  have r := cell_differential_bound de hb (by norm_num) t ht
  rw [zero,norm_zero] at r
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using r) (norm_nonneg _)))

theorem joined_identification {N : ℕ} {a : State} {s : ℝ} (hs : |s|≤1/100)
    {x : ℕ→ℝ→State} (jx : Joined N a x)
    (dx : ∀i,i<N→FollowsState s (x i))
    (bx : ∀i,i<N→∀t∈unitCell,StateBox (x i t)) :
    ∀i,i<N→∀t∈unitCell,x i t=wideFlow (((i:ℝ)+t)*s,a) := by
  intro i
  induction i with
  | zero =>
    intro hi t ht
    have eq : x 0 0=wideFlow (0,a) := by simpa [wideFlow_zero] using jx 0 hi
    simpa only [Nat.cast_zero,zero_add] using cell_identification hs a eq (dx 0 hi) (bx 0 hi) t ht
  | succ i ih =>
    intro hi t ht
    have li : i<N := by omega
    have he : x (i+1) 0=wideFlow (((i:ℝ)+1)*s,a) := by
      simpa [ih li 1 (by norm_num [unitCell])] using jx (i+1) hi
    have hd := cell_identification hs a he (dx (i+1) hi) (bx (i+1) hi) t ht
    rw [show ((↑(i+1):ℝ)+t)*s=((i:ℝ)+1)*s+t*s by push_cast; ring]
    exact hd

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.joined_identification
