import SolitonClassification.Rotating.ResetFrechet
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A common initial-state flow family on an open ball, with genuine Fréchet
derivatives and uniform centre and cube budgets, using integer tape checks. -/
theorem shooting_family {n : ℤ} (T : PolynomialTape n 4000) (hs : |step n|≤1/125)
    (origin : matrixPath (T.data 0) 0=1) :
    ∃X : State→ℕ→ℝ→State, ∀a∈ball (path (T.data 0) d 0) (2/10^30),
      Joined 4000 a (X a) ∧ (∀i,i<4000→FollowsState (step n) (X a i)) ∧
      ∀i,i<4000→∀t∈unitCell,
      ‖X a i t-path (T.data i) d t‖≤5/10^26 ∧
      (‖a-path (T.data 0) d 0‖≤1/10^71 → ‖X a i t-path (T.data i) d t‖≤5/10^52) ∧
      HasFDerivAt (fun b=>X b i t) (fderiv ℝ (fun b=>X b i t) a) a ∧
      ‖fderiv ℝ (fun b=>X b i t) a-matrixPath (T.data i) t‖≤3/10^12 := by
  classical
  let Q := fun i=>path (T.data i) d
  let S := ball (Q 0 0) (2/10^30)
  have mv (a : State) : Ring.inverse (matrixPath (T.data 0) 0) (a-Q 0 0)=a-Q 0 0 := by rw [origin,Ring.inverse_one];rfl
  let Sol (a : State) (x : ℕ→ℝ→State) := Joined 4000 a x ∧ (∀i,i<4000→FollowsState (step n) (x i)) ∧
    ∀i,i<4000→∀t∈unitCell,‖x i t-Q i t‖≤5/10^26 ∧
      (‖a-Q 0 0‖≤1/10^71 → ‖x i t-Q i t‖≤5/10^52)
  have exist (a : State) (hin : a∈S) : ∃x,Sol a x := by
    by_cases f : ‖a-Q 0 0‖≤1/10^71
    · obtain ⟨x,hx⟩:=centre_tape T hs a (by rw [mv];exact f)
      refine ⟨x,fun i hi=>(hx i hi).1,fun i hi=>(hx i hi).2.1,fun i hi t ht=>?_⟩
      exact ⟨((hx i hi).2.2 t ht).trans (by norm_num),fun _=>(hx i hi).2.2 t ht⟩
    · have p : ‖a-Q 0 0‖<2/10^30 := by simpa only [S,mem_ball,dist_eq_norm] using hin
      obtain ⟨x,hx⟩:=cube_tape T hs a (by rw [mv];exact p.le)
      exact ⟨x,fun i hi=>(hx i hi).1,fun i hi=>(hx i hi).2.1,fun i hi t ht=>⟨(hx i hi).2.2 t ht,fun g=>(f g).elim⟩⟩
  let X (a : State) := if had : a∈S then (exist a had).choose else fun _ _=>a
  have sol (a : State) (ha : a∈S) : Sol a (X a) := by dsimp only [X];rw [dif_pos ha];exact (exist a ha).choose_spec
  have box (a : State) (hin : a∈S) (i : ℕ) (hi : i<4000) (t : ℝ) (ht : t∈unitCell) : StateBox (X a i t) := by
    intro j hj
    have q:= (lift_inner (T.small i hi) ht).1 j hj
    change |Q i t j|≤9 at q
    have er:= (coordinate_bound (X a i t-Q i t) j).trans ((sol a hin).2.2 i hi t ht).1
    change |X a i t j-Q i t j|≤_ at er
    have ab:=abs_add_le (X a i t j-Q i t j) (Q i t j)
    rw [sub_add_cancel] at ab
    linarith only [q,er,ab]
  refine ⟨X,?_⟩
  intro a had
  have ha : a∈S := had
  have base := sol a ha
  obtain ⟨J,j⟩:=tape_variation T (by decide) hs (X a) (by norm_num : (5:ℝ)/10^26≤1)
    base.2.1 (fun i hi t ht=>(base.2.2 i hi t ht).1) variation_budget_cube.1 variation_budget_cube.2.1
  have jini : JoinedMatrix 4000 J := fun i hi=>by simpa only [origin] using (j i hi).1
  have nb : S∈𝓝 a := isOpen_ball.mem_nhds ha
  have diam (b : State) (hb : b∈S) (i : ℕ) (hi : i<4000) (t : ℝ) (ht : t∈unitCell) :
      ‖X b i t-X a i t‖≤1 := by
    have tri:=norm_sub_le_norm_sub_add_norm_sub (X b i t) (Q i t) (X a i t)
    rw [norm_sub_rev (Q i t) (X a i t)] at tri
    exact tri.trans ((add_le_add ((sol b hb).2.2 i hi t ht).1 (base.2.2 i hi t ht).1).trans (by norm_num))
  have diff:=actual_endpoint_fderiv (hs.trans (by norm_num)) nb X (fun b hb=>(sol b hb).1)
    (fun b hb=>(sol b hb).2.1) box diam J jini (fun i hi=>(j i hi).2.1)
  refine ⟨base.1,base.2.1,fun i hi t ht=>⟨(base.2.2 i hi t ht).1,(base.2.2 i hi t ht).2,?_,?_⟩⟩
  · exact (diff i hi t ht).differentiableAt.hasFDerivAt
  · rw [(diff i hi t ht).fderiv]
    have num : (i:ℝ)+1≤4000 := by exact_mod_cast (show i+1≤4000 by omega)
    have pos : 0≤2*coefficientBound (5/(10:ℝ)^26) := by norm_num [coefficientBound,eps]
    exact ((j i hi).2.2 t ht).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left num (by norm_num)) pos).trans variation_budget_cube.2.2)
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.shooting_family
