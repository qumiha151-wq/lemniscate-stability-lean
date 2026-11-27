import LengthGrowth.ActualFlow.MulticoverOutwardClosure
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Set Filter Topology MeasureTheory Function
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Outward
open LengthGrowth.ActualFlow

/-- Every sufficiently high boundary at each sufficiently high winding
has a true smooth unit-speed closed immersed position with outward rate. -/
theorem high_winding_outward :
    ∃R:ℝ,1≤R ∧ ∀(m:ℕ) (K:ℝ),1000*R≤(m:ℝ) → 30000*R*(m:ℝ)≤K →
    ∃g:PeriodicRegularPosition,materialSignedCurvature g.position g.period=2*Real.pi*(m:ℝ) ∧
      2*materialEnergy g.position g.period*g.length-(2*Real.pi*(m:ℝ))^2=K ∧
      0<materialEnergy g.position g.period*materialLengthRate g.position g.period-
        g.length*materialDissipation g.position g.period:=by
  obtain ⟨R,hr,hR⟩:=block_uniform
  refine ⟨R,hr,fun m K hm hK=>?_⟩
  obtain ⟨u,hu,hit,good⟩:=crosses_every_high_boundary blockIntegrals R hr hR
    (fun m=>(block_defect_continuous m).continuousOn) hm hK
  let v:=blockIntegrals u
  have err:=hR u hu
  have ha:=abs_le.mp err.1
  change -R≤v.turn ∧ v.turn≤R at ha
  have n1 : 1≤m:=by
    by_contra! bad
    have z:m=0:=by omega
    subst m
    norm_num at hm
    linarith
  let n:ℕ:=(m-1)/2
  let p:ℕ:=2*n+1
  have pp : p≤m ∧ m≤p+1:=by dsimp only [p,n];omega
  have pm : (p:ℝ)≤(m:ℝ):=by exact_mod_cast pp.1
  have mp : (m:ℝ)≤(p:ℝ)+1:=by exact_mod_cast pp.2
  have turn : 1≤Real.pi*(p:ℝ)-v.turn:=by
    have b:=mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Nat.cast_nonneg p : 0≤(p:ℝ))
    linarith
  let T:=Real.pi*(m:ℝ)-v.turn
  let a:Layout u:=
    {half:=u+2+(Real.pi*(p:ℝ)-v.turn),period:=2*(u+2+T),
     two:=by linarith only [hu,hr],gap:=by linarith only [turn],
     extra:=by dsimp [T];linarith only [mul_le_mul_of_nonneg_left pm Real.pi_pos.le]}
  have aP : a.period=2*(u+2+T):=rfl
  have aH : a.half=u+2+(Real.pi*(p:ℝ)-v.turn):=rfl
  have first:=a.half_integral .turn
  change a.angle a.half=v.turn+(a.half-(u+2))*1 at first
  rw [aH] at first
  have hemi : a.angle a.half=Real.pi*(p:ℝ):=by rw [aH];linarith only [first]
  have full:=a.full_integral .turn
  change a.angle a.period=2*v.turn+(a.period-2*(u+2))*1 at full
  have total : a.angle a.period=2*Real.pi*(m:ℝ):=by
    rw [full,aP];dsimp [T];ring
  have halfrot : rotation (a.angle a.half)= -1:=by
    rw [hemi,show Real.pi*(p:ℝ)=2*Real.pi*(n:ℝ)+Real.pi by dsimp [p];push_cast;ring,
      rotation_add,rotation_turn,rotation_pi,one_mul]
  have allrot : rotation (a.angle a.period)=1:=by rw [total,rotation_turn]
  have ds : deriv a.angle=a.curveK:=funext fun x=>(primitive_derivative a.smooth.continuous x).deriv
  obtain ⟨g,gp,gL,gS,gE,gJ,gD⟩:=realize_angle a.period (by linarith only [a.hp]) a.angle a.curveK
    (primitive_smooth a.smooth) ds (a.angle_per allrot) (a.closed halfrot allrot)
  have B:=a.full_integral .square
  have J:=a.full_integral .rate
  have D:=a.full_integral .diss
  let f:=fun s=>deriv (deriv a.curveK) s+a.curveK s^3/2
  change (∫s in 0..a.period,a.curveK s^2)=2*v.square+(a.period-2*(u+2))*1^2 at B
  change (∫s in 0..a.period,a.curveK s*f s)=2*v.rate+(a.period-2*(u+2))*(1*(1/2)) at J
  change (∫s in 0..a.period,f s^2)=2*v.diss+(a.period-2*(u+2))*(1/2)^2 at D
  change materialLengthRate g.position g.period=∫s in 0..a.period,a.curveK s*f s at gJ
  change materialDissipation g.position g.period=∫s in 0..a.period,f s^2 at gD
  change materialSignedCurvature g.position g.period=a.angle a.period at gS
  rw [B] at gE
  rw [J] at gJ
  rw [D] at gD
  refine ⟨g,gS.trans total,?_,?_⟩
  · rw [gE,gL,aP]
    change defect (m:ℝ) u v=K at hit
    rw [←hit]
    dsimp only [defect,T]
    ring
  · rw [gE,gJ,gD,gL,aP]
    change 0<outwardRate (m:ℝ) u v at good
    apply good.trans_eq
    dsimp only [outwardRate,T]
    ring

/-- The positive material derivative gives actual exit at all sufficiently
small positive times for any smooth physical evolution starting at the data. -/
theorem leaves_boundary (c:ForwardImmersion) (hf:c.IsNormalFEF) (M K:ℝ)
    (hit : 2*c.normalizedProduct 0-M^2=K)
    (out : 0<c.energy 0*c.lengthRate 0-c.length 0*c.dissipation 0) :
    ∀ᶠt in 𝓝[>] (0:ℝ),K<2*c.normalizedProduct t-M^2:=by
  have d:=(c.normalizedProduct_right_derivative hf (le_refl 0)).mono (show Ioi (0:ℝ)⊆Ici 0 from Ioi_subset_Ici_self)
  have slopepos:=((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0:ℝ))).mp d).eventually_const_lt out
  filter_upwards [self_mem_nhdsWithin,slopepos] with t ht hs
  rw [slope_def_field] at hs
  have inc:=(div_pos_iff_of_pos_right (sub_pos.mpr ht)).mp hs
  linarith only [inc,hit]

end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.high_winding_outward
#print axioms LengthGrowth.Multicover.Outward.leaves_boundary
