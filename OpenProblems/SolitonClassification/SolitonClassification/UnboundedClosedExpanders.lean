import SolitonClassification.MatchCertifiedSeam
import SolitonClassification.PhysicalCentreSelector
import SolitonClassification.PhysicalIncomingWinding
import SolitonClassification.CentrePhaseContinuity

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set Filter MeasureTheory OuterStress ReflectedArc
open scoped Topology

/-- The first physical crossing retained by the centre chart. Time is
recorded in both physical arclength and the outer slow variable. -/
structure CentreChart.FirstIncoming {H E B : ℝ} (c : CentreChart H E B) where
  slow : Ici B → ℝ
  arclength : ∀ b : Ici B, c.time b = slow b/Real.sqrt (b:ℝ)⁻¹
  time_bounds : ∀ b, 1 < slow b ∧ slow b ≤ 10000
  earlier : ∀ b : Ici B, ∀ t∈Ico (1:ℝ) (slow b), H < -height (centreAt b t)
  segment : ∀ b : Ici B, ∀ t∈Icc (1:ℝ) (slow b), regular (centreAt b t) ∧
    1 ≤ innerRoot (centreAt b t) ∧ 1/12000000 ≤ along (centreAt b t) ∧
    (1/scale (centreAt b t)^4)^3 ≤ 1200^4*((b:ℝ)⁻¹)^2
  crossing : ∀ b : Ici B, -height (centreAt b (slow b))=H

/-- The section height may exceed any prescribed threshold. Both the first
centre crossing and the physical duration of the remaining seam arc are
recorded on the same pair of charts used for the winding match. -/
theorem exists_physical_shooting_charts_with_geometry (requested : ℝ) :
    ∃ H E B : ℝ, requested≤H ∧ 32≤B ∧ ∃ w : WindingChart H E, ∃ c : CentreChart H E B,
      (∀ b : Ici B, (b:ℝ)/8 ≤ c.angle b) ∧ Nonempty w.Flight ∧ Nonempty c.FirstIncoming := by
  obtain ⟨Hc,charts⟩ := exists_winding_chart_with_flight
  obtain ⟨K,kp,Hs,hs,select⟩ := physical_centre_selector
  let H := max (max (max Hs Hc) (1000*K)) requested
  have h1 : Hs≤H := (le_max_left ..).trans ((le_max_left ..).trans (le_max_left ..))
  have h2 : Hc≤H := (le_max_right ..).trans ((le_max_left ..).trans (le_max_left ..))
  have Hpos : 0<H := by linarith
  have KH : K/H≤0.001 := (div_le_iff₀ Hpos).mpr (by
    linarith [show 1000*K≤H from (le_max_right ..).trans (le_max_left ..)])
  obtain ⟨E,ep,w,flight⟩ := charts H h2
  have limit : Tendsto (fun b : ℝ => 1200^4*(b⁻¹)^2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.pow 2).const_mul (1200^4:ℝ)
  obtain ⟨N,ncap⟩ := eventually_atTop.mp (limit.eventually_lt_const (by positivity : (0:ℝ)<E^3))
  obtain ⟨B,lower,T,τ,ct,info⟩ := select H h1 N
  have b32 (b : Ici B) : 32≤(b:ℝ) := (le_max_left ..).trans (lower.trans b.property)
  have bpos (b : Ici B) : 0<(b:ℝ) := lt_of_lt_of_le (by norm_num) (b32 b)
  let s := fun b : Ici B => τ b/Real.sqrt (b:ℝ)⁻¹
  let x := fun b : Ici B => centreAt b (τ b)
  let z := fun b : Ici B => centreData b (bpos b)
  let angle := fun b : Ici B => ∫ u in (0:ℝ)..τ b, Angle.spin (b:ℝ)⁻¹ (z b).root
    (z b).shape (z b).slope (z b).along (z b).across u
  have slab (b : Ici B) (u : ℝ) (hu : u ∈ Icc 1 (τ b)) :
      regular (centreAt b u) ∧ 1≤ innerRoot (centreAt b u) := by
    have r := (info b).2.2.2.2.2.1 u ⟨hu.1,hu.2.trans (info b).2.1.2.le⟩
    exact ⟨r.1,r.2.1⟩
  have atCross (b : Ici B) := (info b).2.2.2.2.2.1 (τ b) (Ioo_subset_Icc_self (info b).2.1)
  have rg (b : Ici B) : regular (x b) := (atCross b).1
  have sp (b : Ici B) : 0<scale (x b) := Real.rpow_pos_of_pos (rg b).1 _
  have ce : Continuous (fun b : Ici B => (![0,(b:ℝ),0,0] : Phase)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  have ctime : Continuous s :=
    ct.div ((continuous_subtype_val.inv₀ (fun b => (bpos b).ne')).sqrt)
      (fun b => (Real.sqrt_pos.mpr (inv_pos.mpr (bpos b))).ne')
  have cx : Continuous x := continuous_solution.comp (ctime.prodMk (continuous_const.prodMk ce))
  have css : Continuous (fun b : Ici B => scale (x b)) := by
    have r : Continuous (fun b : Ici B => radiusSquared (x b)) :=
      (((continuous_apply 2).comp cx).pow 2).add (((continuous_apply 3).comp cx).pow 2)
    exact r.rpow_const fun b => Or.inl (rg b).1.ne'
  have ceps : Continuous (fun b : Ici B => 1/(scale (x b))^4) :=
    continuous_const.div (css.pow 4) (fun b => pow_ne_zero 4 (sp b).ne')
  have epsmem (b : Ici B) : 1/(scale (x b))^4 ∈ Icc (0:ℝ) E := by
    have cap := (atCross b).2.2.2
    have small := ncap b ((le_max_right ..).trans (lower.trans b.property))
    refine ⟨one_div_nonneg.mpr (pow_nonneg (sp b).le _),?_⟩
    exact le_of_pow_le_pow_left₀ (by decide : (3:ℕ)≠0) ep.le (cap.trans small.le)
  let eps := fun b : Ici B => (⟨1/(scale (x b))^4,epsmem b⟩ : Icc (0:ℝ) E)
  have phase (b : Ici B) := winding_on_physical_strip (b32 b) (info b).2.1.1.le (slab b)
  have cr : Continuous angle := centre_phase_continuous (fun b : Ici B => (b:ℝ)) τ
    continuous_subtype_val ct bpos (fun b => zero_le_one.trans (info b).2.1.1.le)
    (fun b => positive_amplitude_on_physical_strip (b32 b) (slab b))
  let ch : CentreChart H E B := {
    time := s, angle := angle, eps := eps, transverse := fun b => impact (x b),
    contAngle := cr, contEps := ceps.subtype_mk _,
    contImpact := continuous_iff_continuousAt.mpr fun b => (impact_continuousAt (rg b)).comp cx.continuousAt,
    winding := by
      intro D hD v
      let b : Ici B := ⟨max D (8*v+8),hD.trans (le_max_left ..)⟩
      refine ⟨b,le_max_left ..,?_⟩
      have lo : 8*v+8 ≤ (b:ℝ) := le_max_right .. 
      have hi : (b:ℝ)/8 ≤ angle b := (phase b).1
      linarith,
    small := fun b => (info b).2.2.2.2.1.trans KH,
    physical := by
      intro b
      have A := outer_chart (inv_pos.mpr (bpos b)) _ (solution_derivative 1 (![0,(b:ℝ),0,0] : Phase)) (τ b) (rg b)
      have a := (phase b).2
      change (z b).shape (τ b)/Real.sqrt 2=Real.sin (angle b) ∧
        (z b).slope (τ b)/Real.sqrt (1+((z b).shape (τ b))^2/2)=Real.cos (angle b) at a
      have U : (z b).shape (τ b) = shape (x b) := A.2.1
      have W : (z b).slope (τ b) = slope (x b) := A.2.2.1
      rw [U,W] at a
      have ps : 0<s b := div_pos (lt_trans zero_lt_one (info b).2.1.1) (Real.sqrt_pos.mpr (inv_pos.mpr (bpos b)))
      exact ⟨ps,rg b,(info b).2.2.2.1,le_trans (by norm_num) (atCross b).2.2.1,
        one_div_pos.mpr (pow_pos (sp b) _),rfl,by simpa only [s, centreSlice, centreAt, neg_neg] using congrArg Neg.neg (info b).2.2.1,rfl,a.1.symm,a.2.symm⟩ }
  refine ⟨H,E,B,le_max_right ..,(le_max_left ..).trans lower,w,ch,fun b => (phase b).1,
    flight,⟨⟨τ,fun _ => rfl,?_,?_,?_,?_⟩⟩⟩
  · exact fun b => ⟨(info b).2.1.1,(info b).2.1.2.le.trans (info b).1⟩
  · exact fun b => (info b).2.2.2.2.2.2.2
  · exact fun b t ht => (info b).2.2.2.2.2.1 t ⟨ht.1,ht.2.trans (info b).2.1.2.le⟩
  · exact fun b => (info b).2.2.1

/-- A common physical section with a continuous centre chart on a full tail
    of markers and a uniform linear lower bound on its real angle lift. -/
theorem exists_physical_shooting_charts :
    ∃ H E B : ℝ, 32≤B ∧ ∃ _w : WindingChart H E, ∃ c : CentreChart H E B,
      ∀ b : Ici B, (b:ℝ)/8 ≤ c.angle b := by
  obtain ⟨H,E,B,_,b32,w,c,lo,_,_⟩ := exists_physical_shooting_charts_with_geometry 0
  exact ⟨H,E,B,b32,w,c,lo⟩

/-- Arbitrarily large curvature slopes occur on actual, smooth, closed
    coefficient-one homothetic expanders of turning number zero. -/
theorem unbounded_closed_zero_turn_expanders (requested : ℝ) :
    ∃ b > requested, ∃ L > (0:ℝ), Nonempty (ZeroTurnExpander L b) := by
  obtain ⟨H,E,B,_,w,ch,_⟩ := exists_physical_shooting_charts
  obtain ⟨b,hb,L,hL,h⟩ := ch.closes w (max B (requested+1)) (le_max_left ..)
  exact ⟨b,by linarith [le_max_right B (requested+1)],L,hL,h⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.unbounded_closed_zero_turn_expanders
