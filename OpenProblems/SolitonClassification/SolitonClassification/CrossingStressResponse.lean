import SolitonClassification.SupportFlowContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace ClosedSimilarity.CrossingResponse
open GlobalSupport

/-- Fast central shot, with state `(K,V,εY·N,εY·T)`. -/
def shot (e t : ℝ) := solution e ![0,1,0,0] t
def K (e t : ℝ) := shot e t 0
def V (e t : ℝ) := shot e t 1
private def p (e t : ℝ) := shot e t 2
private def q (e t : ℝ) := shot e t 3
private def prim (f : ℝ → ℝ → ℝ) (e t : ℝ) := ∫ r in (0:ℝ)..t, f e r
def angle := prim K
def tx (e t : ℝ) := Real.cos (angle e t)
def ty (e t : ℝ) := Real.sin (angle e t)
def X := prim tx
def Y := prim ty
def stressX (e t : ℝ) := K e t ^ 2 / 2 * tx e t - V e t * ty e t
def stressY (e t : ℝ) := K e t ^ 2 / 2 * ty e t + V e t * tx e t
def horizontalRate (e t : ℝ) := (-X e t * ty e t + Y e t * tx e t) * ty e t

private theorem coord_cont (i : Fin 4) : Continuous (fun z : ℝ × ℝ => shot z.1 z.2 i) := by
  have c : Continuous (fun z : ℝ × ℝ => (z.2,(z.1,(![0,1,0,0] : Phase)))) :=
    continuous_snd.prodMk (continuous_fst.prodMk continuous_const)
  exact (continuous_apply i).comp (continuous_solution.comp c)

private theorem primitive_cont (f : ℝ → ℝ → ℝ) (cf : Continuous f.uncurry) :
    Continuous (fun z : ℝ × ℝ => prim f z.1 z.2) := by
  have c : Continuous (fun z : (ℝ × ℝ) × ℝ => f z.1.1 z.2) :=
    cf.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) (f := fun z : ℝ × ℝ => f z.1) c continuous_snd

theorem angle_cont : Continuous (fun z : ℝ × ℝ => angle z.1 z.2) := primitive_cont K (coord_cont 0)
theorem tx_cont : Continuous (fun z : ℝ × ℝ => tx z.1 z.2) := Real.continuous_cos.comp angle_cont
theorem ty_cont : Continuous (fun z : ℝ × ℝ => ty z.1 z.2) := Real.continuous_sin.comp angle_cont
theorem X_cont : Continuous (fun z : ℝ × ℝ => X z.1 z.2) := primitive_cont tx tx_cont
theorem Y_cont : Continuous (fun z : ℝ × ℝ => Y z.1 z.2) := primitive_cont ty ty_cont
theorem horizontalRate_cont : Continuous horizontalRate.uncurry :=
  (((X_cont.neg.mul ty_cont).add (Y_cont.mul tx_cont))).mul ty_cont

private theorem time_cont (f : ℝ → ℝ → ℝ) (cf : Continuous f.uncurry) (e : ℝ) :
    Continuous (f e) := cf.comp (continuous_const.prodMk continuous_id)

private theorem prim_der (f : ℝ → ℝ → ℝ) (cf : Continuous f.uncurry) (e t : ℝ) :
    HasDerivAt (prim f e) (f e t) t :=
  intervalIntegral.integral_hasDerivAt_right ((time_cont f cf e).intervalIntegrable 0 t)
    (time_cont f cf e).aestronglyMeasurable.stronglyMeasurableAtFilter (time_cont f cf e).continuousAt

private theorem dynamics (e t : ℝ) :
    HasDerivAt (K e) (V e t) t ∧ HasDerivAt (V e) (-(K e t)^3/2-p e t) t ∧
    HasDerivAt (p e) (-K e t*q e t) t ∧ HasDerivAt (q e) (e+K e t*p e t) t := by
  have h := hasDerivAt_pi.mp (solution_derivative e (![0,1,0,0] : Phase) t)
  exact ⟨h 0,h 1,h 2,h 3⟩

private theorem frame_d (e t : ℝ) :
    HasDerivAt (tx e) (-ty e t * K e t) t ∧ HasDerivAt (ty e) (tx e t * K e t) t := by
  have a := prim_der K (coord_cont 0) e t
  exact ⟨a.cos,a.sin⟩

private theorem same_primitive {f g : ℝ → ℝ} (F : ℝ → ℝ) (cF : Continuous F)
    (hf : ∀ t, HasDerivAt f (F t) t) (hg : ∀ t, HasDerivAt g (F t) t)
    (init : f 0 = g 0) (t : ℝ) : f t = g t := by
  have a := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t) (fun s _ => hf s) (cF.intervalIntegrable 0 t)
  have b := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t) (fun s _ => hg s) (cF.intervalIntegrable 0 t)
  linarith

private theorem components (e t : ℝ) :
    q e t * tx e t - p e t * ty e t = e * X e t ∧
    q e t * ty e t + p e t * tx e t = e * Y e t := by
  constructor
  · refine same_primitive (f := fun s => q e s*tx e s-p e s*ty e s) (g := fun s => e*X e s)
      (fun s => e * tx e s) ((time_cont tx tx_cont e).const_mul e) ?_ ?_
      (by simp [q,p,shot,solution_zero,X,prim]) t
    · intro s
      obtain ⟨_,_,dp,dq⟩ := dynamics e s
      obtain ⟨dx,dy⟩ := frame_d e s
      convert! (dq.mul dx).sub (dp.mul dy) using 1; ring
    · intro s; exact (prim_der tx tx_cont e s).const_mul e
  · refine same_primitive (f := fun s => q e s*ty e s+p e s*tx e s) (g := fun s => e*Y e s)
      (fun s => e * ty e s) ((time_cont ty ty_cont e).const_mul e) ?_ ?_
      (by simp [q,p,shot,solution_zero,Y,prim]) t
    · intro s
      obtain ⟨_,_,dp,dq⟩ := dynamics e s
      obtain ⟨dx,dy⟩ := frame_d e s
      convert! (dq.mul dy).add (dp.mul dx) using 1; ring
    · intro s; exact (prim_der ty ty_cont e s).const_mul e

private theorem actual_p (e t : ℝ) : p e t = e * (-X e t * ty e t + Y e t * tx e t) := by
  obtain ⟨a,b⟩ := components e t
  have un : ty e t ^ 2 + tx e t ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  linear_combination -ty e t * a + tx e t * b - p e t * un

theorem stressX_exact (e t : ℝ) : stressX e t = e * prim horizontalRate e t := by
  apply same_primitive (fun s => e * horizontalRate e s) ((time_cont _ horizontalRate_cont e).const_mul e) _ _
    (by simp [stressX,K,V,shot,solution_zero,ty,angle,prim])
  · intro s
    obtain ⟨dk,dv,_,_⟩ := dynamics e s
    obtain ⟨dx,dy⟩ := frame_d e s
    change HasDerivAt (fun t => K e t^2 / 2 * tx e t - V e t * ty e t) _ s
    convert! ((((dk.pow 2).div_const 2).mul dx).sub (dv.mul dy)) using 1
    rw [actual_p]; unfold horizontalRate; simp only [Pi.pow_apply]; ring
  · intro s; exact (prim_der _ horizontalRate_cont e s).const_mul e

/-- Along any endpoint continuous at zero, the parameter derivative of
    the actual horizontal fast stress equals its frozen forcing integral. -/
theorem stressX_response (r : ℝ → ℝ) (hr : ContinuousAt r 0) :
    HasDerivAt (fun e => stressX e (r e)) (∫ t in (0:ℝ)..r 0, horizontalRate 0 t) 0 := by
  have c := (primitive_cont _ horizontalRate_cont).continuousAt (x := ((0:ℝ),r 0))
  have h : ContinuousAt (fun e : ℝ => prim horizontalRate e (r e)) 0 :=
    c.comp (f := fun e : ℝ => (e,r e)) (continuousAt_id.prodMk hr)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply Filter.Tendsto.congr' _ (h.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with e he
  have ne : e ≠ 0 := he
  simp [stressX_exact, smul_eq_mul, ne]

private theorem frozen_stressY (t : ℝ) : stressY 0 t = 1 := by
  refine same_primitive (f := stressY 0) (g := fun _ => 1) (fun _ => 0) continuous_const ?_
    (fun s => hasDerivAt_const s 1) (by simp [stressY,K,V,shot,solution_zero,tx,angle,prim]) t
  intro s
  obtain ⟨dk,dv,_,_⟩ := dynamics 0 s
  obtain ⟨dx,dy⟩ := frame_d 0 s
  change HasDerivAt (fun t => K 0 t^2 / 2 * ty 0 t + V 0 t * tx 0 t) _ s
  convert! ((((dk.pow 2).div_const 2).mul dy).add (dv.mul dx)) using 1
  rw [actual_p]; simp only [Pi.pow_apply, zero_mul]; ring

theorem frozen_tangent (t : ℝ) : tx 0 t = V 0 t ∧ ty 0 t = K 0 t ^ 2 / 2 := by
  have wx : K 0 t^2/2 * tx 0 t - V 0 t * ty 0 t = 0 := by
    change stressX 0 t = 0; rw [stressX_exact, zero_mul]
  have wy : K 0 t^2/2 * ty 0 t + V 0 t * tx 0 t = 1 := frozen_stressY t
  have un : ty 0 t ^ 2 + tx 0 t ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  constructor
  · linear_combination ty 0 t * wx - tx 0 t * wy + V 0 t * un
  · linear_combination -tx 0 t * wx - ty 0 t * wy + (K 0 t ^ 2 / 2) * un

theorem frozen_positionX (t : ℝ) : X 0 t = K 0 t := by
  refine same_primitive (f := X 0) (g := K 0) (V 0) (time_cont V (coord_cont 1) 0)
    ?_ (fun s => (dynamics 0 s).1) (by simp [X,prim,K,shot,solution_zero]) t
  intro s; rw [← (frozen_tangent s).1]; exact prim_der tx tx_cont 0 s

theorem frozen_data :
    Continuous (V 0) ∧ (∀ t, HasDerivAt (K 0) (V 0 t) t) ∧
      (∀ t, HasDerivAt (Y 0) (K 0 t ^ 2 / 2) t) ∧ K 0 0 = 0 := by
  refine ⟨time_cont V (coord_cont 1) 0, fun t => (dynamics 0 t).1, ?_, ?_⟩
  · intro t; rw [← (frozen_tangent t).2]; exact prim_der ty ty_cont 0 t
  · simp [K,shot,solution_zero]

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.stressX_response
#print axioms ClosedSimilarity.CrossingResponse.frozen_data
