import Migration.ForceLobeTurn

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop

private theorem ordered_levels {g : ℝ→ℝ} (cg : Continuous g) {s t : ℝ} (st : s≤t)
    (n : ℕ) (rise : (n:ℝ)*Real.pi ≤ g t-g s) :
    ∃ τ : Fin (n+1)→ℝ, StrictMono τ ∧
      ∀i, τ i∈Icc s t ∧ g (τ i)=g s+(i.val:ℝ)*Real.pi := by
  let H := fun i : Fin (n+1) => g s+(i.val:ℝ)*Real.pi
  have inc : StrictMono H := by
    intro i j ij
    dsimp only [H]
    have a := mul_lt_mul_of_pos_right (show (i.val:ℝ)<j.val by exact_mod_cast ij) Real.pi_pos
    linarith
  have low (i : Fin (n+1)) : g s≤H i := by dsimp [H]; exact le_add_of_nonneg_right (by positivity)
  have upper (i : Fin (n+1)) : H i≤g t := by
    have le : i.val≤n := by omega
    have m := mul_le_mul_of_nonneg_right (show (i.val:ℝ)≤n by exact_mod_cast le) Real.pi_pos.le
    dsimp [H]; linarith
  have first (i : Fin (n+1)) : ∃x∈Icc s t,g x=H i ∧
      ∀y∈Icc s t,g y=H i→x≤y := by
    let K := Icc s t ∩ g ⁻¹' {H i}
    have ck : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage cg)
    obtain ⟨v,hv,ev⟩ := intermediate_value_Icc st cg.continuousOn ⟨low i,upper i⟩
    obtain ⟨x,hx,mn⟩ := ck.exists_isMinOn (show K.Nonempty from ⟨v,hv,ev⟩) continuous_id.continuousOn
    exact ⟨x,hx.1,hx.2,fun y hy ey=>mn (show y∈K from ⟨hy,ey⟩)⟩
  choose τ memτ eqτ minτ using first
  refine ⟨τ,?_,fun i=>⟨memτ i,eqτ i⟩⟩
  intro i j ij
  have less := inc ij
  obtain ⟨u,hu,eu⟩ := intermediate_value_Icc (memτ j).1 cg.continuousOn
    (show H i∈Icc (g s) (g (τ j)) from ⟨low i,(eqτ j) ▸ less.le⟩)
  have le := (minτ i u ⟨hu.1,hu.2.trans (memτ j).2⟩ eu).trans hu.2
  exact lt_of_le_of_ne le (fun e=>less.ne ((eqτ i).symm.trans ((congrArg g e).trans (eqτ j))))

variable {L : ℝ} (c : UnitLoop L)

/-- A single material period contains N successive intervals whose endpoint
values of the true force have opposite strict signs. -/
def alternatingForceVisits (N : ℕ) : Prop :=
  ∃s : ℝ, ∃τ : Fin (N+1)→ℝ, StrictMono τ ∧ (∀i,τ i∈Icc s (s+L)) ∧
    ∀i : Fin N,c.F (τ i.castSucc)*c.F (τ i.succ)<0

theorem signed_cover_of_few_force_changes {m : ℕ} (mp : 0<m) (lp : 0<L)
    (turn : 2*Real.pi*(m:ℝ)≤|∫s in (0:ℝ)..L,c.k s|)
    (few : ¬c.alternatingForceVisits (2*m)) : c.signedNormalCover 0 := by
  intro U V unit
  by_contra bad
  push Not at bad
  obtain ⟨θ,d,phase⟩ := c.tangent_phase
  have one : 2*Real.pi≤|∫s in (0:ℝ)..L,c.k s| := by
    have mi : (1:ℝ)≤m := by exact_mod_cast mp
    nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr mi) Real.pi_pos.le]
  obtain ⟨s,_,nx,ny⟩ := c.every_normal_of_full_turn lp.le one unit
  have ct : Continuous θ := continuous_iff_continuousAt.mpr fun x=>(d x).continuousAt
  have per := (signedCurvature_periodic c.px c.py).intervalIntegral_add_eq s 0
  simp only [zero_add] at per
  have diff := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=s) (b:=s+L) (fun v _=>d v)
    (c.contK.intervalIntegrable ..)
  change (∫v in s..s+L,c.k v)=(∫v in (0:ℝ)..L,c.k v) at per
  rw [←per,diff] at turn
  let n := 2*m
  have samples : ∃τ : Fin (n+1)→ℝ, StrictMono τ ∧ (∀i,τ i∈Icc s (s+L)) ∧
      ∀i, θ (τ i)=θ s+(i.val:ℝ)*Real.pi ∨ θ (τ i)=θ s-(i.val:ℝ)*Real.pi := by
    rcases le_abs.mp turn with pos|neg
    · obtain ⟨τ,mono,h⟩ := ordered_levels ct (show s≤s+L by linarith) n (by dsimp [n]; push_cast; linarith only [pos])
      exact ⟨τ,mono,fun i=>(h i).1,fun i=>Or.inl (h i).2⟩
    · obtain ⟨τ,mono,h⟩ := ordered_levels ct.neg (show s≤s+L by linarith) n (by dsimp [n]; push_cast; linarith only [neg])
      exact ⟨τ,mono,fun i=>(h i).1,fun i=>Or.inr (by have e := (h i).2; change -θ (τ i)= -θ s+(i.val:ℝ)*Real.pi at e; linarith only [e])⟩
  obtain ⟨τ,mono,mem,angles⟩ := samples
  have orientation (i : Fin (n+1)) :
      -deriv c.y (τ i)=(-1:ℝ)^i.val*U ∧ deriv c.x (τ i)=(-1:ℝ)^i.val*V := by
    have aty := (phase (τ i)).2
    have atx := (phase (τ i)).1
    rcases angles i with eq|eq
    · rw [eq,Real.sin_add_nat_mul_pi,(phase s).2] at aty
      rw [eq,Real.cos_add_nat_mul_pi,(phase s).1,ny] at atx
      exact ⟨by rw [←aty,←nx]; ring,atx.symm⟩
    · rw [eq,Real.sin_sub_nat_mul_pi,(phase s).2] at aty
      rw [eq,Real.cos_sub_nat_mul_pi,(phase s).1,ny] at atx
      exact ⟨by rw [←aty,←nx]; ring,atx.symm⟩
  have sign (i : Fin (n+1)) : (-1:ℝ)^i.val*c.F (τ i)<0 := by
    rcases neg_one_pow_eq_or ℝ i.val with pos|neg
    · have h:=orientation i; rw [pos,one_mul,one_mul] at h
      rw [pos,one_mul]; exact bad.1 (τ i) h.1 h.2
    · have h:=orientation i; rw [neg,neg_one_mul,neg_one_mul] at h
      rw [neg,neg_one_mul]; have plus:=bad.2 (τ i) h.1 h.2; linarith
  apply few
  refine ⟨s,τ,mono,mem,?_⟩
  intro i
  have first := sign i.castSucc
  have next := sign i.succ
  simp only [Fin.val_castSucc,Fin.val_succ,pow_succ,mul_neg_one] at first next
  rcases neg_one_pow_eq_or ℝ i.val with pos|neg
  · rw [pos] at first next; simp only [one_mul,neg_one_mul,neg_lt_zero] at first next
    exact mul_neg_of_neg_of_pos first next
  · rw [neg] at first next; simp only [neg_one_mul,neg_neg,one_mul,neg_lt_zero] at first next
    exact mul_neg_of_pos_of_neg first next

end MigrationGeometry.Rotating.UnitLoop
#print axioms MigrationGeometry.Rotating.UnitLoop.signed_cover_of_few_force_changes
