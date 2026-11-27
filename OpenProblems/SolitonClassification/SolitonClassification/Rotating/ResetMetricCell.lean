import SolitonClassification.Rotating.ResetQuadratic
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
abbrev unitCell := Icc (0:ℝ) 1

/-- Polynomial reference data plus verifiable inequalities on one time cell. -/
structure MetricCell (s : ℝ) where
  Q : ℝ→State
  dQ : ℝ→State
  M : ℝ→FlowEnd
  dM : ℝ→FlowEnd
  state_deriv : ∀t,HasDerivAt Q (dQ t) t
  variation_deriv : ∀t,HasDerivAt M (dM t) t
  derivative_cont : Continuous dQ
  inner : ∀t∈unitCell, ∀i : Fin 6,i.val<5 → |Q t i|≤9
  state_res : ∀t∈unitCell,‖dQ t-s • field (Q t)‖≤eps
  var_res : ∀t∈unitCell,‖dM t-(s • fderiv ℝ field (Q t))*M t‖≤6*eps
  unit : ∀t∈unitCell,IsUnit (M t)
  matrix_norm : ∀t∈unitCell,‖M t‖≤5000
  inverse_norm : ∀t∈unitCell,‖Ring.inverse (M t)‖≤5000

def FollowsState (s : ℝ) (x : ℝ→State) := ∀t∈unitCell,
  HasDerivWithinAt x (s • field (x t)) unitCell t

private theorem zlin (a : State) : linear a 0=0 := by
  rw [←field_fderiv_apply,map_zero]

theorem MetricCell.local_solution {s : ℝ} (c : MetricCell s) (hs : |s|≤1/100)
    (a : State) (ha : ‖a-c.Q 0‖≤1/4) :
    ∃x : ℝ→State,x 0=a ∧ FollowsState s x ∧ ∀t∈unitCell,‖x t-c.Q t‖≤3*‖a-c.Q 0‖+2*eps := by
  let q : ℝ→Aug := fun t=>(c.Q t,0)
  let dq : ℝ→Aug := fun t=>(c.dQ t,0)
  let e : Aug := (a-c.Q 0,0)
  have Qd (t : ℝ) : HasDerivAt q (dq t) t := (c.state_deriv t).prodMk (hasDerivAt_const _ _)
  have cd : Continuous dq := c.derivative_cont.prodMk continuous_const
  have cond (t : ℝ) (ht : t∈unitCell) : Inner (q t) ∧ ‖dq t-s • augmented (q t)‖≤eps := by
    constructor
    · exact ⟨c.inner t ht,by intro j i; norm_num [q]⟩
    · rw [Prod.norm_def,max_le_iff]
      exact ⟨c.state_res t ht,by simp [dq,q,augmented,zlin,eps]; change ‖s • (0:Fin 5→State)‖≤_; simp⟩
  have en : ‖e‖=‖a-c.Q 0‖ := by simp [e,Prod.norm_def]
  obtain ⟨x,hx,hd,bd⟩ := signed_shadow_cell hs Qd cd cond e (en ▸ ha)
  refine ⟨fun t=>(x t).1,?_,fun t ht => (hd t ht).fst,?_⟩
  · change (x 0).1=a;rw [hx];simp [q,e]
  · intro t ht
    exact (norm_fst_le (x t-q t)).trans ((bd t ht).trans_eq (by rw [en]))

theorem reconstruct_error {M : FlowEnd} (hu : IsUnit M) (v : State) :
    v=M (Ring.inverse M v) := (congrArg (fun A : FlowEnd=>A v) (Ring.mul_inverse_cancel M hu)).symm

def roughPhysical (R : ℝ) := 3*(5000*R)+2*eps
def increment (R : ℝ) := 5000*((1/100)*(3*(roughPhysical R)^2)+eps+
  (6*eps)*(5000*roughPhysical R))

/-- One step increases moving-coordinate error by an additive amount. The argument
uses a true original-field initial value problem and a derivative of the actual
inverse matrix applied to its error over the complete closed cell. -/
theorem MetricCell.transport {s : ℝ} (c : MetricCell s) (hs : |s|≤1/100)
    (a : State) {R : ℝ} (hr : 5000*R≤1/4) (hr1 : roughPhysical R≤1)
    (ha : ‖Ring.inverse (c.M 0) (a-c.Q 0)‖≤R) :
    ∃x : ℝ→State,x 0=a ∧ FollowsState s x ∧ ∀t∈unitCell,
      ‖movingError x c.Q c.M t‖≤‖Ring.inverse (c.M 0) (a-c.Q 0)‖+increment R := by
  have zeroIn : (0:ℝ)∈unitCell := by norm_num [unitCell]
  have hn : ‖a-c.Q 0‖≤5000*R := by
    calc
      _ = ‖c.M 0 (Ring.inverse (c.M 0) (a-c.Q 0))‖ := congrArg norm (reconstruct_error (c.unit 0 zeroIn) _)
      _ ≤ _ := ((c.M 0).le_opNorm _).trans (mul_le_mul (c.matrix_norm 0 zeroIn) ha (norm_nonneg _) (by norm_num))
  obtain ⟨x,ini,xd,bd⟩ := c.local_solution hs a (hn.trans hr)
  let res := fun t=>c.dQ t-s • field (c.Q t)
  let defM := fun t=>c.dM t-(s • fderiv ℝ field (c.Q t))*c.M t
  let v := fun t=>bootstrapVelocity s (x t) (c.Q t) (c.M t) (defM t) (res t)
  have vd (t : ℝ) (ht : t∈unitCell) : HasDerivWithinAt (movingError x c.Q c.M) (v t) unitCell t := by
    apply moving_deriv (c.unit t ht) (xd t ht)
    · simpa [res] using (c.state_deriv t).hasDerivWithinAt (s:=unitCell)
    · simpa [defM] using (c.variation_deriv t).hasDerivWithinAt (s:=unitCell)
  have hd (t : ℝ) (ht : t∈unitCell) : ‖x t-c.Q t‖≤roughPhysical R := by
    exact (bd t ht).trans (by dsimp [roughPhysical]; linarith only [hn])
  have vb (t : ℝ) (ht : t∈unitCell) : ‖v t‖≤ increment R := by
    have he := ((Ring.inverse (c.M t)).le_opNorm _).trans
      (mul_le_mul (c.inverse_norm t ht) (hd t ht) (norm_nonneg _) (by norm_num))
    have p := moving_velocity (s:=s) (c.inner t ht 0 (by decide)) (hd t ht) hr1 he
      (c.var_res t ht) (c.state_res t ht) (c.inverse_norm t ht)
    exact p.trans (by unfold increment; gcongr)
  refine ⟨x,ini,xd,?_⟩
  intro t ht
  have step := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le vd vb zeroIn ht
  rw [sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] at step
  have ge := (norm_nonneg _).trans (vb 0 zeroIn)
  have hb := (norm_le_norm_sub_add (movingError x c.Q c.M t) (movingError x c.Q c.M 0)).trans
    (add_le_add_left (step.trans ((mul_le_mul_of_nonneg_left ht.2 ge).trans_eq (mul_one _))) _)
  simpa only [movingError,ini,add_comm] using hb

end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.MetricCell.transport
