import SolitonClassification.Rotating.ResetMetricCell
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- A finite union of cells for either signed direction. The same initial
value is advanced from one cell to the next, in the moving coordinates of
a reference matrix that is exactly continuous at the accepted joins. -/
theorem transport_chain {s : ℝ} (c : ℕ→MetricCell s) (N : ℕ) (a : State)
    {R r : ℝ} (R0 : 0≤R) (hs : |s|≤1/100) (hr : 5000*R≤1/4) (hr1 : roughPhysical R≤1)
    (joins : ∀i,i+1<N → (c i).Q 1=(c (i+1)).Q 0 ∧ (c i).M 1=(c (i+1)).M 0)
    (start : ‖Ring.inverse ((c 0).M 0) (a-(c 0).Q 0)‖≤r)
    (budget : r+(N:ℝ)*increment R≤R) :
    ∃x : ℕ→ℝ→State, ∀i,i<N →
      x i 0=(if i=0 then a else x (i-1) 1) ∧ FollowsState s (x i) ∧
      ∀t∈unitCell,‖movingError (x i) (c i).Q (c i).M t‖≤r+((i:ℝ)+1)*increment R ∧
        ‖x i t-(c i).Q t‖≤5000*R := by
  classical
  have incP : 0≤ increment R := by unfold increment roughPhysical eps; positivity
  let bound := fun i : ℕ => r+(i:ℝ)*increment R
  have small (i : ℕ) (hi : i≤N) : bound i≤R := by
    exact (add_le_add_right (mul_le_mul_of_nonneg_right (show (i:ℝ)≤N by exact_mod_cast hi) incP) r).trans budget
  let good := fun (i : ℕ) (v : State)=>‖Ring.inverse ((c i).M 0) (v-(c i).Q 0)‖≤bound i
  let nextPath (i : ℕ) (v : State) : ℝ→State :=
    if h : i<N ∧ good i v then Classical.choose ((c i).transport hs v hr hr1 (h.2.trans (small i h.1.le)))
    else fun _=>v
  have next (i : ℕ) (v : State) (hi : i<N) (gv : good i v) :
      nextPath i v 0=v ∧ FollowsState s (nextPath i v) ∧
        ∀t∈unitCell,‖movingError (nextPath i v) (c i).Q (c i).M t‖≤bound (i+1) := by
    dsimp only [nextPath]
    rw [dif_pos (show i<N ∧ good i v from ⟨hi,gv⟩)]
    obtain ⟨ini,ode,err⟩ := Classical.choose_spec ((c i).transport hs v hr hr1 (gv.trans (small i hi.le)))
    refine ⟨ini,ode,fun t ht=>(err t ht).trans ?_⟩
    have b := add_le_add_left gv (increment R)
    simpa only [bound,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc] using b
  let node : ℕ→State := Nat.rec a (fun i v=>nextPath i v 1)
  have ng (i : ℕ) (hi : i<N) : good i (node i) := by
    induction i with
    | zero => simpa [good,bound,node] using start
    | succ i ih =>
      have prev := next i (node i) (by omega) (ih (by omega))
      have atEnd := prev.2.2 1 (by norm_num [unitCell])
      obtain ⟨sq,sm⟩ := joins i hi
      change ‖Ring.inverse ((c (i+1)).M 0) (nextPath i (node i) 1-(c (i+1)).Q 0)‖≤_
      simpa only [movingError,sq,sm] using atEnd
  refine ⟨fun i=>nextPath i (node i),?_⟩
  intro i hi
  obtain ⟨ini,ode,err⟩ := next i (node i) hi (ng i hi)
  refine ⟨?_,ode,?_⟩
  · change nextPath i (node i) 0=_; rw [ini];cases i <;> simp [node]
  · intro t ht
    have mid := err t ht
    refine ⟨by simpa [bound] using mid,?_⟩
    have y := mid.trans (small (i+1) (by omega))
    let v := nextPath i (node i) t-(c i).Q t
    calc
      ‖v‖ = ‖(c i).M t (Ring.inverse ((c i).M t) v)‖ :=
        congrArg norm (reconstruct_error ((c i).unit t ht) v)
      _ ≤ _ := (((c i).M t).le_opNorm _).trans
        (mul_le_mul ((c i).matrix_norm t ht) y (norm_nonneg _) (by norm_num))

theorem centre_4000_budget :
    5000*(1/(10:ℝ)^55)≤1/4 ∧ roughPhysical (1/(10:ℝ)^55)≤1 ∧
    1/(10:ℝ)^71+4000*increment (1/(10:ℝ)^55)≤1/(10:ℝ)^55 := by
  norm_num [roughPhysical,increment,eps]

theorem cube_4000_budget :
    5000*(1/(10:ℝ)^29)≤1/4 ∧ roughPhysical (1/(10:ℝ)^29)≤1 ∧
    2/(10:ℝ)^30+4000*increment (1/(10:ℝ)^29)≤1/(10:ℝ)^29 := by
  norm_num [roughPhysical,increment,eps]

end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.transport_chain
