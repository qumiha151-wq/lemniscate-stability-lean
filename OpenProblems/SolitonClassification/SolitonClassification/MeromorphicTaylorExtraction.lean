import SolitonClassification.MeromorphicTaylorApprox
import Mathlib.Algebra.Polynomial.Div

noncomputable section
open Complex Polynomial Filter Set
open scoped Topology Polynomial
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

def sixTerm (c d e f g h:ℂ) : ℂ[X] :=
  C c+X*(C d+X*(C e+X*(C f+X*(C g+X*C h))))

private theorem peel {f:ℂ→ℂ} {x:ℂ} (af:AnalyticAt ℂ f x) :
    ∃g:ℂ→ℂ, AnalyticAt ℂ g x ∧ ∀ᶠ z in 𝓝 x,f z=f x+(z-x)*g z := by
  let v := fun z=>f z-f x
  have av : AnalyticAt ℂ v x := af.sub analyticAt_const
  have non : analyticOrderAt v x≠0 := av.analyticOrderAt_ne_zero.mpr (sub_self _)
  have step : ((1:ℕ):ℕ∞)≤analyticOrderAt v x := Order.one_le_iff_ne_zero.mpr non
  obtain ⟨g,ag,eq⟩ := (natCast_le_analyticOrderAt av).mp step
  refine ⟨g,ag,?_⟩
  filter_upwards [eq] with z e
  change f z-f x=(z-x)^1*g z at e
  rw [pow_one] at e
  linear_combination e

theorem sixTerm_of_jet {f:ℂ→ℂ} {x c:ℂ} {n:ℤ} (j:Jet f x n c) :
    ∃d e t g h:ℂ, Approx x n f (sixTerm c d e t g h) := by
  obtain ⟨y,ay,hx,eq⟩:=j
  obtain ⟨u1,a1,e1⟩:=peel ay
  obtain ⟨u2,a2,e2⟩:=peel a1
  obtain ⟨u3,a3,e3⟩:=peel a2
  obtain ⟨u4,a4,e4⟩:=peel a3
  obtain ⟨u5,a5,e5⟩:=peel a4
  obtain ⟨u6,a6,e6⟩:=peel a5
  refine ⟨u1 x,u2 x,u3 x,u4 x,u5 x,u6,a6,?_⟩
  filter_upwards [eq,e1.filter_mono nhdsWithin_le_nhds,e2.filter_mono nhdsWithin_le_nhds,
    e3.filter_mono nhdsWithin_le_nhds,e4.filter_mono nhdsWithin_le_nhds,
    e5.filter_mono nhdsWithin_le_nhds,e6.filter_mono nhdsWithin_le_nhds] with z hh q1 q2 q3 q4 q5 q6
  rw [hh,q1,q2,q3,q4,q5,q6,hx]
  simp only [sixTerm,eval_add,eval_mul,eval_C,eval_X];ring

theorem Approx.dvd_of_zero {f:ℂ→ℂ} {x:ℂ} {n:ℤ} {P:ℂ[X]}
    (app:Approx x n f P) (zero:f=ᶠ[𝓝[≠] x] fun _=>0) : X^6∣P := by
  by_cases pz:P=0
  · simp [pz]
  obtain ⟨G,fac,nd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd pz 0
  have nz : G.eval 0≠0 := fun hz=>nd (dvd_iff_isRoot.mpr hz)
  simp only [map_zero,sub_zero] at fac
  let m:=P.rootMultiplicity 0
  have ge : 6≤m := by
    by_contra! low
    have ag : AnalyticAt ℂ (fun z=>G.eval (z-x)) x := ((AnalyticOnNhd.eval_polynomial G) 0 (mem_univ _)).comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
    have j : Jet (fun z=>P.eval (z-x)) x m (G.eval 0) := by
      refine ⟨fun z=>G.eval (z-x),ag,by simp,?_⟩
      filter_upwards with z
      rw [fac,eval_mul,eval_pow,eval_X,zpow_natCast]
    obtain ⟨u,au,eq⟩:=app
    have q : Jet (fun z=>P.eval (z-x)) x 6 (-u x) := by
      refine ⟨fun z=> -u z,au.neg,rfl,?_⟩
      filter_upwards [eq,zero,eventually_mem_nhdsWithin] with z h zz ne
      rw [zz] at h
      have m0 := (mul_eq_zero.mp h.symm).resolve_left (zpow_ne_zero _ (sub_ne_zero.mpr ne))
      norm_num
      linear_combination m0
    exact nz (j.unique (q.weaken (by exact_mod_cast low)) (by rfl))
  rw [fac]
  exact dvd_mul_of_dvd_left (pow_dvd_pow X ge) _

theorem Approx.extension_of_dvd {f:ℂ→ℂ} {x:ℂ} {P:ℂ[X]}
    (app:Approx x (-3) f P) (div:X^4∣P) :
    ∃G:ℂ→ℂ,AnalyticAt ℂ G x ∧ G x=0 ∧ f=ᶠ[𝓝[≠] x] G := by
  obtain ⟨Q,q⟩:=div
  obtain ⟨g,ag,e⟩:=app
  have qa : AnalyticAt ℂ (fun z=>Q.eval (z-x)) x := ((AnalyticOnNhd.eval_polynomial Q) 0 (mem_univ _)).comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  refine ⟨fun z=>(z-x)*(Q.eval (z-x)+(z-x)^2*g z),by fun_prop,by simp,?_⟩
  filter_upwards [e,eventually_mem_nhdsWithin] with z h nz
  have diff:=sub_ne_zero.mpr nz
  rw [h,q,eval_mul,eval_pow,eval_X]
  norm_num
  field_simp

end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.Approx.dvd_of_zero
