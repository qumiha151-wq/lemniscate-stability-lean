import SolitonClassification.PrimitiveInflections
import SolitonClassification.CentreCriticalLayer

noncomputable section
set_option maxHeartbeats 1000000
namespace ClosedSimilarity.ReflectedArc.ZeroTurnExpander
open GlobalSupport OuterStress MeasureTheory Set

/-- Across the middle of the initial oscillation interval, the scaled
    position has a definite component along the stress for all high markers. -/
private theorem late_alignment :
    ∃ B≥32, ∀ b≥B, ∃ bp : 0<b, ∀ s ∈ Icc (1/2:ℝ) 1,
      1/1200 < (centreData b bp).along s := by
  obtain ⟨L,hL,C,_,all⟩ := OuterStress.Data.reaches_critical_layer
  refine ⟨32*L,by linarith,?_⟩
  intro b hb
  have Lp : 0<L := by linarith
  have bp : 0<b := by linarith
  let δ := b⁻¹
  let z := centreData b bp
  have hd : 0<δ := inv_pos.mpr bp
  have tiny : δ≤1/(32*L) := by
    dsimp [δ]; rw [←one_div]
    exact one_div_le_one_div_of_le (by positivity) hb
  have zero : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by simp [z,centreData,ofSupport,solution_zero,bp.ne']
  obtain ⟨T,tm,hit,seg⟩ := all L le_rfl z hd tiny zero.1 zero.2.1 zero.2.2.1 zero.2.2.2
  have Tpos : 0≤T := by linarith [tm.1]
  have T1 : 1≤T := by
    by_contra! bad
    have a := (z.centre_bounds hd zero.1 zero.2.1 zero.2.2.1 zero.2.2.2 Tpos).2
    have sq := pow_le_pow_left₀ Tpos bad.le 2
    have rr : z.root T^2=z.amplitude T := Real.sq_sqrt (Real.sqrt_nonneg _)
    have rlo : 1/2≤z.root T := le_of_sq_le_sq (by nlinarith) (Real.sqrt_nonneg _)
    have c := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) rlo 3
    have v := (le_div_iff₀ (by positivity : 0<32*L)).mp tiny
    nlinarith
  exact ⟨bp,fun s hs => (seg s ⟨hs.1,hs.2.trans T1⟩).1⟩

/-- Opposite large physical forces can occur at exactly the same curvature,
    on every sufficiently high-marker normalized profile. -/
theorem opposite_force_at_inflections :
    ∃ B≥32, ∀ {L b : ℝ}, B≤b → ∀ P : ZeroTurnExpander L b,
      ∃ s t : ℝ, P.k s=0 ∧ P.k t=0 ∧ deriv P.k s≠0 ∧ deriv P.k t≠0 ∧
        deriv (deriv P.k) s < -Real.sqrt b/1200 ∧ Real.sqrt b/1200 < deriv (deriv P.k) t := by
  obtain ⟨A,a32,uniform⟩ := late_alignment
  refine ⟨max A (48*Real.pi),a32.trans (le_max_left ..),?_⟩
  intro L b largeB P
  have large : 32≤b := a32.trans ((le_max_left ..).trans largeB)
  have room : 48*Real.pi≤b := (le_max_right ..).trans largeB
  obtain ⟨bp,alignment⟩ := uniform b ((le_max_left ..).trans largeB)
  let δ := b⁻¹
  let z := centreData b bp
  have hd : 0<δ := inv_pos.mpr bp
  have small : δ≤1/32 := by change b⁻¹≤_; rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) large
  have init : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  obtain ⟨hk,hv,hp,hq⟩ := init
  have bounds (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      Rates δ x z.root z.shape z.slope z.along z.across ∧ |z.along x|≤1 ∧ |z.across x|≤1 ∧
      4*1*δ≤z.root x^3 ∧ 1/2≤z.root x := by
    obtain ⟨pq,amp⟩ := z.centre_bounds hd hk hv hp hq hx.1
    have x2 := pow_le_pow_left₀ hx.1 hx.2 2
    have lower : 1/2≤z.amplitude x := by nlinarith
    have apos : 0<z.amplitude x := by linarith
    have rsq : z.root x^2=z.amplitude x := Real.sq_sqrt apos.le
    have pos : 0≤z.root x := Real.sqrt_nonneg _
    have rlo : 1/2≤z.root x := le_of_sq_le_sq (by nlinarith) pos
    have r3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) rlo 3
    have frame := z.radius_sq x apos
    refine ⟨z.normalized_rates x apos hd,?_,?_,by linarith,rlo⟩
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]
  let g := Angle.spin δ z.root z.shape z.slope z.along z.across
  let θ := fun x : ℝ => ∫ t in (0:ℝ)..x, g t
  have cg : ContinuousOn g (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact fun x hx => (Angle.spin_continuousAt (bounds x hx).1).continuousWithinAt
  have ct : ContinuousOn θ (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using intervalIntegral.continuousOn_primitive_interval
      (cg.integrableOn_compact isCompact_uIcc (μ := volume))
  have st : (1/2:ℝ)≤1 := by norm_num
  have early : (0:ℝ)≤1/2 := by norm_num
  have inc := Angle.winding_on_interval st (fun x hx => bounds x ⟨early.trans hx.1,hx.2⟩)
  have integr : IntervalIntegrable g volume 0 1 := cg.intervalIntegrable
  have add := intervalIntegral.integral_add_adjacent_intervals
    (integr.mono_set (show uIcc 0 (1/2:ℝ) ⊆ uIcc 0 1 by simp only [uIcc_of_le early,uIcc_of_le zero_le_one]; exact Icc_subset_Icc_right st))
    (integr.mono_set (show uIcc (1/2:ℝ) 1 ⊆ uIcc 0 1 by simp only [uIcc_of_le st,uIcc_of_le zero_le_one]; exact Icc_subset_Icc_left early))
  have span : θ (1/2)+3*Real.pi≤θ 1 := by
    have e : b/16≤∫ t in (1/2:ℝ)..1, g t := by convert inc using 1; dsimp [δ]; field_simp; norm_num
    change θ (1/2)+(∫ t in (1/2:ℝ)..1,g t)=θ 1 at add
    linarith
  let n : ℤ := ⌈θ (1/2)/(2*Real.pi)⌉
  let v := (n:ℝ)*(2*Real.pi)
  have pp : 0<2*Real.pi := by positivity
  have low : θ (1/2)≤v := (div_le_iff₀ pp).mp (Int.le_ceil _)
  have high : v<θ (1/2)+2*Real.pi := by
    have h : (n:ℝ)< θ (1/2)/(2*Real.pi)+1 := Int.ceil_lt_add_one _
    have h' := (lt_div_iff₀ pp).mp (show (n:ℝ)-1<θ (1/2)/(2*Real.pi) by linarith)
    dsimp [v]; linarith
  have mid := intermediate_value_Icc st (ct.mono (Icc_subset_Icc_left early))
  obtain ⟨x,hx,ex⟩ := mid (show v∈Icc (θ (1/2)) (θ 1) from ⟨low,by linarith [Real.pi_pos]⟩)
  obtain ⟨y,hy,ey⟩ := mid (show v+Real.pi∈Icc (θ (1/2)) (θ 1) from ⟨by linarith [Real.pi_pos],by linarith⟩)
  have sinV : Real.sin v=0 := by
    convert Real.sin_int_mul_pi (2*n) using 2; push_cast; dsimp [v]; ring
  have cosV : Real.cos v=1 := Real.cos_int_mul_two_pi n
  let f := Real.sqrt δ
  have fp : 0<f := Real.sqrt_pos.mpr hd
  have recip : 1/f=Real.sqrt b := by simp [f,δ,Real.sqrt_inv]
  let force := fun u => deriv (deriv P.k) (u/f)
  have atZero (u : ℝ) (hu : u∈Icc (1/2:ℝ) 1) (sn : Real.sin (θ u)=0) :
      P.k (u/f)=0 ∧ z.along u = Real.cos (θ u)*(-f*force u) := by
    have rg := bounds u ⟨early.trans hu.1,hu.2⟩
    have point := ((physical_centre_winding large).1 u ⟨early.trans hu.1,hu.2⟩).2
    change Angle.sn z.shape u=Real.sin (θ u) ∧ Angle.cs z.shape z.slope u=Real.cos (θ u) at point
    have canon : z.shape u=0 := (div_eq_zero_iff.mp (point.1.trans sn)).resolve_right (by positivity)
    have zeroK : z.K u=0 := (div_eq_zero_iff.mp canon).resolve_right rg.1.pos.ne'
    have cs : z.slope u=Real.cos (θ u) := by simpa [Angle.cs,canon] using point.2
    have support := congrFun P.cartesianSupport_eq_solution (u/f)
    have K : z.K u=f*P.k (u/f) := by change f*(solution 1 ![0,b,0,0] (u/f) 0)=_; rw [←support]; rfl
    have pk := (mul_eq_zero.mp (K.symm.trans zeroK)).resolve_left fp.ne'
    have F := P.dilation_equation (u/f)
    rw [pk] at F
    have p : z.p u = -f*force u := by
      change f*(solution 1 ![0,b,0,0] (u/f) 2)=_
      rw [←support]
      change f*(-P.X (u/f)*deriv P.Y (u/f)+P.Y (u/f)*deriv P.X (u/f))= -f*deriv (deriv P.k) (u/f)
      linear_combination f * F
    refine ⟨pk,?_⟩
    rw [←cs,←p]
    simp only [Data.along,Data.radial,Data.slope,zeroK,zero_pow (by decide : 2≠0),zero_div,zero_mul,zero_add]
    ring
  obtain ⟨kx,ax⟩ := atZero x hx (ex ▸ sinV)
  obtain ⟨ky,ay⟩ := atZero y hy (by rw [ey,Real.sin_add_pi,sinV,neg_zero])
  rw [ex,cosV,one_mul] at ax
  rw [ey,Real.cos_add_pi,cosV,neg_one_mul,neg_mul,neg_neg] at ay
  have a := alignment x hx
  have c := alignment y hy
  change 1/1200<z.along x at a
  change 1/1200<z.along y at c
  have rf : f*Real.sqrt b=1 := by rw [←recip,one_div,mul_inv_cancel₀ fp.ne']
  have simple (u : ℝ) (hu : u∈Icc (1/2:ℝ) 1) (ku : P.k (u/f)=0) : deriv P.k (u/f)≠0 := by
    intro flat
    have eq := congrFun P.cartesianSupport_eq_solution (u/f)
    have K : z.K u=0 := by
      change f*(solution 1 ![0,b,0,0] (u/f) 0)=0
      rw [←eq]; change f*P.k (u/f)=0; rw [ku,mul_zero]
    have V : z.V u=0 := by
      change δ*(solution 1 ![0,b,0,0] (u/f) 1)=0
      rw [←eq]; change δ*deriv P.k (u/f)=0; rw [flat,mul_zero]
    have rp := (bounds u ⟨early.trans hu.1,hu.2⟩).1.pos
    simp [Data.root,Data.amplitude,K,V] at rp
  refine ⟨x/f,y/f,kx,ky,simple x hx kx,simple y hy ky,?_,?_⟩
  · apply lt_of_mul_lt_mul_left (a:=f) _ fp.le
    change f*force x<f*(-Real.sqrt b/1200)
    nlinarith only [ax,a,rf]
  · apply lt_of_mul_lt_mul_left (a:=f) _ fp.le
    change f*(Real.sqrt b/1200)<f*force y
    nlinarith only [ay,c,rf]

end ClosedSimilarity.ReflectedArc.ZeroTurnExpander
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.opposite_force_at_inflections

namespace ClosedSimilarity.GlobalSupport.MovingSeam
open ReflectedArc

/-- No choice of a scalar function of curvature can approximate the physical
    elastic force uniformly across the normalized closed zero-turn family. -/
theorem unbounded_error_for_every_curvature_law (M : ℝ) :
    ∃ b>0, ∃ L>0, ∃ P : ZeroTurnExpander L b, ∀ G : ℝ → ℝ,
      ∃ s, P.k s=0 ∧ deriv P.k s≠0 ∧
        M < |deriv (deriv P.k) s+(P.k s)^3/2-G (P.k s)| := by
  obtain ⟨B,b32,split⟩ := ZeroTurnExpander.opposite_force_at_inflections
  let A := max 0 M+1
  obtain ⟨b,high,L,lp,⟨P⟩⟩ := unbounded_closed_zero_turn_expanders (max B ((1200*A)^2))
  have bb : B≤b := (le_max_left ..).trans high.le
  have bp : 0<b := by linarith
  have big : A<Real.sqrt b/1200 := by
    by_contra! low
    have sq := pow_le_pow_left₀ (Real.sqrt_nonneg b) (show Real.sqrt b≤1200*A by linarith) 2
    rw [Real.sq_sqrt bp.le] at sq
    exact (not_lt_of_ge sq) ((le_max_right ..).trans_lt high)
  have ma : M<A := by dsimp [A]; linarith [le_max_right 0 M]
  obtain ⟨s,t,ks,kt,ds,dt,small,large⟩ := split bb P
  refine ⟨b,bp,L,lp,P,?_⟩
  intro G
  by_cases sign : 0≤G 0
  · refine ⟨s,ks,ds,?_⟩
    rw [ks]; simp only [zero_pow (by decide : 3≠0),zero_div,add_zero]
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
  · refine ⟨t,kt,dt,?_⟩
    rw [kt]; simp only [zero_pow (by decide : 3≠0),zero_div,add_zero]
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.unbounded_error_for_every_curvature_law
