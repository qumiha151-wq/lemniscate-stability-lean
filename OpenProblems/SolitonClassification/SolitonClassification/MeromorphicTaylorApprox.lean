import SolitonClassification.MeromorphicOrdinaryPole
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision

noncomputable section
open Complex Polynomial Filter Set
open scoped Topology Polynomial
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

/-- Six consecutive Laurent coefficients are represented by P; terms of
polynomial degree six or higher have no influence on the approximation. -/
def Approx (x:ℂ) (n:ℤ) (f:ℂ→ℂ) (P:ℂ[X]) : Prop :=
  ∃g:ℂ→ℂ, AnalyticAt ℂ g x ∧ ∀ᶠ z in 𝓝[≠] x,
    f z=(z-x)^n*(P.eval (z-x)+(z-x)^6*g z)

def polyStep (n:ℤ) (P:ℂ[X]) := C (n:ℂ)*P+X*P.derivative

namespace Approx
variable {x:ℂ} {n m:ℤ} {P Q:ℂ[X]} {f g:ℂ→ℂ}

theorem add (h:Approx x n f P) (j:Approx x n g Q) : Approx x n (fun z=>f z+g z) (P+Q) := by
  obtain ⟨u,a,eq⟩:=h;obtain ⟨v,b,er⟩:=j
  refine ⟨fun z=>u z+v z,a.add b,?_⟩
  filter_upwards [eq,er] with z e d
  rw [e,d,eval_add];ring

theorem sub (h:Approx x n f P) (j:Approx x n g Q) : Approx x n (fun z=>f z-g z) (P-Q) := by
  obtain ⟨u,a,eq⟩:=h;obtain ⟨v,b,er⟩:=j
  refine ⟨fun z=>u z-v z,a.sub b,?_⟩
  filter_upwards [eq,er] with z e d
  rw [e,d,eval_sub];ring

theorem smul (h:Approx x n f P) (c:ℂ) : Approx x n (fun z=>c*f z) (C c*P) := by
  obtain ⟨u,a,eq⟩:=h
  refine ⟨fun z=>c*u z,analyticAt_const.mul a,?_⟩
  filter_upwards [eq] with z e
  rw [e,eval_mul,eval_C];ring

theorem mul (h:Approx x n f P) (j:Approx x m g Q) : Approx x (n+m) (fun z=>f z*g z) (P*Q) := by
  obtain ⟨u,a,eq⟩:=h;obtain ⟨v,b,er⟩:=j
  have pa : AnalyticAt ℂ (fun z=>P.eval (z-x)) x := ((AnalyticOnNhd.eval_polynomial P) 0 (mem_univ _)).comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  have qa : AnalyticAt ℂ (fun z=>Q.eval (z-x)) x := ((AnalyticOnNhd.eval_polynomial Q) 0 (mem_univ _)).comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  refine ⟨fun z=>P.eval (z-x)*v z+Q.eval (z-x)*u z+(z-x)^6*u z*v z,by fun_prop,?_⟩
  filter_upwards [eq,er,eventually_mem_nhdsWithin] with z e d nz
  rw [e,d,eval_mul,zpow_add₀ (sub_ne_zero.mpr nz)];ring

theorem pow (h:Approx x n f P) (r:ℕ) : Approx x (r*n) (fun z=>f z^r) (P^r) := by
  induction r with
  | zero => refine ⟨fun _=>0,analyticAt_const,?_⟩;simp
  | succ r ih => simpa only [Nat.cast_succ,add_mul,one_mul,pow_succ] using ih.mul h

theorem shift (h:Approx x (n+(m:ℤ)) f P) (nonneg:0≤m) : Approx x n f (X^m.toNat*P) := by
  obtain ⟨u,a,eq⟩:=h
  refine ⟨fun z=>(z-x)^m.toNat*u z,by fun_prop,?_⟩
  filter_upwards [eq,eventually_mem_nhdsWithin] with z e nz
  have ex : (z-x)^m=(z-x)^m.toNat := by rw [←zpow_natCast,Int.toNat_of_nonneg nonneg]
  rw [e,eval_mul,eval_pow,eval_X,zpow_add₀ (sub_ne_zero.mpr nz),ex]
  ring

theorem deriv_step (h:Approx x n f P) : Approx x (n-1) (deriv f) (polyStep n P) := by
  obtain ⟨u,au,eq⟩:=h
  refine ⟨fun z=>((n:ℂ)+6)*u z+(z-x)*deriv u z,by fun_prop,?_⟩
  have eql : f=ᶠ[𝓝[≠] x] (fun z=>(z-x)^n*(P.eval (z-x)+(z-x)^6*u z)) := eq
  filter_upwards [eql.nhdsNE_deriv,au.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z e uz nz
  have ne := sub_ne_zero.mpr nz
  have dt : HasDerivAt (fun t:ℂ=>t-x) 1 z := (hasDerivAt_id z).sub_const x
  have dp := (P.hasDerivAt (z-x)).comp z dt
  have da := ((hasDerivAt_zpow n (z-x) (Or.inl ne)).comp z dt).fun_mul
    (dp.fun_add ((dt.pow 6).fun_mul uz.differentiableAt.hasDerivAt))
  have split : (z-x)^n=(z-x)^(n-1)*(z-x) := by
    rw [←zpow_add_one₀ ne];congr 1;omega
  rw [e,show deriv (fun t=>(t-x)^n*(P.eval (t-x)+(t-x)^6*u t)) z = _ from da.deriv]
  simp only [Pi.pow_apply,Function.comp_apply,Nat.cast_ofNat,Nat.reduceSub,mul_one,polyStep,eval_add,eval_mul,eval_C,eval_X]
  rw [split];ring

end Approx
end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.Approx.deriv_step
