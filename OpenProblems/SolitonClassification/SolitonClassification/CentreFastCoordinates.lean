import SolitonClassification.CentreRayLimit
import SolitonClassification.CrossingStressResponse
import SolitonClassification.PhysicalSeamScale

noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory
namespace ClosedSimilarity.CrossingResponse
open GlobalSupport OuterStress

theorem slow_fast_curvature {b : ℝ} (bp : 0<b) (u : ℝ) :
    (centreData b bp).K u=K ((b^2)⁻¹) (b*u) := by
  let r := Real.sqrt b
  have rp : 0<r := Real.sqrt_pos.mpr bp
  have sq : r^2=b := Real.sq_sqrt bp.le
  have scale : r^4*(b^2)⁻¹=1 := by
    rw [show r^4=(r^2)^2 by ring,sq]; exact mul_inv_cancel₀ (pow_ne_zero _ bp.ne')
  have initial : restore r ![0,1,0,0]=![0,b,0,0] := by
    funext i; fin_cases i <;> simp [restore,sq]
  have act := physical_support_conjugacy scale (![0,1,0,0] : Phase) (u/Real.sqrt b⁻¹)
  have time : r*(u/Real.sqrt b⁻¹)=b*u := by
    rw [Real.sqrt_inv,div_inv_eq_mul]
    change r*(u*r)=b*u
    linear_combination u*sq
  rw [initial,time] at act
  have coord := congrFun act 0
  change solution 1 ![0,b,0,0] (u/Real.sqrt b⁻¹) 0=r*K ((b^2)⁻¹) (b*u) at coord
  change Real.sqrt b⁻¹*(solution 1 ![0,b,0,0] (u/Real.sqrt b⁻¹) 0)=_
  rw [coord,Real.sqrt_inv]
  change r⁻¹*(r*_)=_
  field_simp [rp.ne']

private theorem same_by_rate {f g F : ℝ → ℝ} (cF : Continuous F)
    (hf : ∀ t, HasDerivAt f (F t) t) (hg : ∀ t, HasDerivAt g (F t) t)
    (init : f 0=g 0) (t : ℝ) : f t=g t := by
  have a := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t) (fun s _ => hf s) (cF.intervalIntegrable ..)
  have b := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t) (fun s _ => hg s) (cF.intervalIntegrable ..)
  linarith

private theorem integral_rate (F : ℝ → ℝ) (h : Continuous F) (s : ℝ) :
    HasDerivAt (fun t => ∫ x in 0..t,F x) (F s) s :=
  intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable ..)
    h.aestronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt

theorem slow_fast_angle {b : ℝ} (bp : 0<b) (u : ℝ) :
    (centreData b bp).laboratoryAngle u=angle ((b^2)⁻¹) (b*u) := by
  let e := (b^2)⁻¹
  let z := centreData b bp
  have ck : Continuous (K e) := continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_pi.mp (solution_derivative e (![0,1,0,0] : Phase) t) 0).continuousAt)
  apply same_by_rate (F:=fun x => b*K e (b*x)) ((ck.comp (continuous_const.mul continuous_id)).const_mul b) _ _
    (by rw [mul_zero]; change (∫ x in (0:ℝ)..0,z.K x/b⁻¹)=(∫ x in (0:ℝ)..0,K e x); simp)
  · intro x
    have h := z.laboratoryAngle_rate x
    rw [show z.K x=K e (b*x) from slow_fast_curvature bp x] at h
    convert h using 1; field_simp
  · intro x
    have a : HasDerivAt (angle e) (K e (b*x)) (b*x) := integral_rate _ ck _
    convert! a.comp x ((hasDerivAt_id x).const_mul b) using 1
    ring

/-- The fixed initial-tangent frame is identical on both clocks. Slow position
is fast position divided by b; the fast time at slow time u is b*u. -/
theorem slow_fast_position {b : ℝ} (bp : 0<b) (u : ℝ) :
    let z := centreData b bp
    z.labX z.laboratoryAngle u=b⁻¹*X ((b^2)⁻¹) (b*u) ∧
    z.labY z.laboratoryAngle u=b⁻¹*Y ((b^2)⁻¹) (b*u) := by
  let e := (b^2)⁻¹
  let z := centreData b bp
  have phase (x : ℝ) := slow_fast_angle bp x
  have embed : Continuous (fun t : ℝ => ((e,t):ℝ×ℝ)) := continuous_const.prodMk continuous_id
  have ct := tx_cont.comp embed
  have cs := ty_cont.comp embed
  change Continuous (tx e) at ct
  change Continuous (ty e) at cs
  have rates (x : ℝ) := z.lab_rates (z.laboratoryAngle_rate x) (inv_pos.mpr bp)
  have xzero : X e 0=0 := by change (∫ x in (0:ℝ)..0,tx e x)=0; simp
  have yzero : Y e 0=0 := by change (∫ x in (0:ℝ)..0,ty e x)=0; simp
  have init : z.p 0=0 ∧ z.q 0=0 := by simp [z,centreData,ofSupport,solution_zero]
  constructor
  · apply same_by_rate (f:=z.labX z.laboratoryAngle) (g:=fun x => b⁻¹*X e (b*x)) (F:=fun x => tx e (b*x)) (ct.comp (continuous_const.mul continuous_id)) _ _
      (by simp [Data.labX,init,xzero])
    · intro x
      simpa only [z,phase,tx,e] using (rates x).1
    · intro x
      have a : HasDerivAt (X e) (tx e (b*x)) (b*x) := integral_rate _ ct _
      convert! (a.comp x ((hasDerivAt_id x).const_mul b)).const_mul b⁻¹ using 1
      field_simp [bp.ne']
  · apply same_by_rate (f:=z.labY z.laboratoryAngle) (g:=fun x => b⁻¹*Y e (b*x)) (F:=fun x => ty e (b*x)) (cs.comp (continuous_const.mul continuous_id)) _ _
      (by simp [Data.labY,init,yzero])
    · intro x
      simpa only [z,phase,ty,e] using (rates x).2
    · intro x
      have a : HasDerivAt (Y e) (ty e (b*x)) (b*x) := integral_rate _ cs _
      convert! (a.comp x ((hasDerivAt_id x).const_mul b)).const_mul b⁻¹ using 1
      field_simp [bp.ne']

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.slow_fast_position



