import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.RationalCurvature

/-- A Laurent coefficient with no negative-order terms below it.
A zero coefficient is permitted, so several expansions can be compared at
the same integer exponent. Equality is only required off the center. -/
def Jet (f : ℂ → ℂ) (x : ℂ) (n : ℤ) (c : ℂ) : Prop :=
  ∃ g : ℂ → ℂ,AnalyticAt ℂ g x ∧ g x=c ∧
    f =ᶠ[𝓝[≠] x] fun z => (z-x)^n*g z

namespace Jet
variable {f g : ℂ → ℂ} {x c d : ℂ} {n m : ℤ}

theorem retag (h : Jet f x n c) (k : n=m) (v : c=d) : Jet f x m d := k ▸ v ▸ h

theorem of_analytic (h : AnalyticAt ℂ f x) : Jet f x 0 (f x) :=
  ⟨f,h,rfl,by simp⟩

theorem of_order (h : MeromorphicAt f x) (ord : meromorphicOrderAt f x=↑n) :
    ∃ c≠0,Jet f x n c := by
  obtain ⟨g,ga,gn,eq⟩ := (meromorphicOrderAt_eq_int_iff h).mp ord
  exact ⟨g x,gn,g,ga,rfl,by simpa only [Filter.EventuallyEq,smul_eq_mul] using eq⟩

theorem unique (h : Jet f x n c) (k : Jet g x n d) (eq : f=ᶠ[𝓝[≠] x]g) : c=d := by
  obtain ⟨a,ha,rfl,ea⟩ := h
  obtain ⟨b,hb,rfl,eb⟩ := k
  apply tendsto_nhds_unique_of_eventuallyEq (l:=𝓝[≠] x) ha.continuousAt.continuousWithinAt hb.continuousAt.continuousWithinAt
  filter_upwards [eq,ea,eb,eventually_mem_nhdsWithin] with z e p q nz
  have hn : z-x ≠ 0 := sub_ne_zero.mpr nz
  exact mul_left_cancel₀ (zpow_ne_zero n hn) (p.symm.trans (e.trans q))

theorem congr (h : Jet f x n c) (eq : g=ᶠ[𝓝[≠] x]f) : Jet g x n c := by
  obtain ⟨a,ha,hx,ea⟩ := h
  exact ⟨a,ha,hx,eq.trans ea⟩

theorem zero (x : ℂ) (n : ℤ) : Jet (fun _=>0) x n 0 :=
  ⟨fun _=>0,analyticAt_const,rfl,by simp⟩

theorem eq_zero_of_germ_zero (h : Jet f x n c) (eq : f=ᶠ[𝓝[≠] x] fun _=>0) : c=0 :=
  h.unique (zero x n) eq

theorem add (h : Jet f x n c) (k : Jet g x n d) :
    Jet (fun z=>f z+g z) x n (c+d) := by
  obtain ⟨a,ha,rfl,ea⟩ := h
  obtain ⟨b,hb,rfl,eb⟩ := k
  exact ⟨fun z=>a z+b z,ha.add hb,rfl,by
    filter_upwards [ea,eb] with z e₁ e₂
    rw [e₁,e₂,mul_add]⟩

theorem sub (h : Jet f x n c) (k : Jet g x n d) :
    Jet (fun z=>f z-g z) x n (c-d) := by
  obtain ⟨a,ha,rfl,ea⟩ := h
  obtain ⟨b,hb,rfl,eb⟩ := k
  exact ⟨fun z=>a z-b z,ha.sub hb,rfl,by
    filter_upwards [ea,eb] with z e₁ e₂
    rw [e₁,e₂,mul_sub]⟩

theorem mul (h : Jet f x n c) (k : Jet g x m d) :
    Jet (fun z=>f z*g z) x (n+m) (c*d) := by
  obtain ⟨a,ha,rfl,ea⟩ := h
  obtain ⟨b,hb,rfl,eb⟩ := k
  refine ⟨fun z=>a z*b z,ha.mul hb,rfl,?_⟩
  filter_upwards [ea,eb,eventually_mem_nhdsWithin] with z e₁ e₂ nz
  rw [e₁,e₂,zpow_add₀ (sub_ne_zero.mpr nz)]
  ring

theorem smul (h : Jet f x n c) (r : ℂ) : Jet (fun z=>r*f z) x n (r*c) := by
  simpa only [zero_add] using
    (of_analytic (x:=x) (f:=fun _=>r) analyticAt_const).mul h

theorem pow (h : Jet f x n c) (r : ℕ) : Jet (fun z=>f z^r) x ((r:ℤ)*n) (c^r) := by
  induction r with
  | zero => simpa using (of_analytic (x:=x) (f:=fun _=>1) analyticAt_const)
  | succ r ih => simpa only [Nat.cast_succ,add_mul,one_mul,pow_succ] using ih.mul h

theorem weaken (h : Jet f x n c) (hm : m<n) : Jet f x m 0 := by
  obtain ⟨a,ha,_,ea⟩ := h
  let j := (n-m).toNat
  have hj : (j:ℤ)=n-m := Int.toNat_of_nonneg (by omega)
  have pos : 0<j := by omega
  refine ⟨fun z=>(z-x)^j*a z,by fun_prop,by simp [zero_pow pos.ne'],?_⟩
  filter_upwards [ea,eventually_mem_nhdsWithin] with z e nz
  have nz' := sub_ne_zero.mpr nz
  rw [e,←mul_assoc,←zpow_natCast,←zpow_add₀ nz',hj]
  congr 2
  omega

theorem deriv (h : Jet f x n c) : Jet (deriv f) x (n-1) ((n:ℂ)*c) := by
  obtain ⟨a,ha,rfl,ea⟩ := h
  refine ⟨fun z=>(n:ℂ)*a z+(z-x)*deriv a z,by fun_prop,by simp,?_⟩
  filter_upwards [ea.nhdsNE_deriv,ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z eq haz nz
  have hn : z-x≠0 := sub_ne_zero.mpr nz
  have dz := (hasDerivAt_zpow n (z-x) (Or.inl hn)).comp z ((hasDerivAt_id z).sub_const x)
  have dv := dz.fun_mul haz.differentiableAt.hasDerivAt
  rw [eq]
  have split : (z-x)^(n-1)*(z-x)=(z-x)^n := by
    rw [←zpow_add_one₀ hn]
    congr 1
    omega
  rw [show deriv (fun t=>(t-x)^n*a t) z =
    (n*(z-x)^(n-1)*1)*a z+(z-x)^n*deriv a z by simpa only [Function.comp_def,id_eq,mul_one] using! dv.deriv]
  rw [←split]
  ring

end Jet
/-- Complexified arclength differentiation on the frequency circle. -/
def euler (μ : ℂ) (f : ℂ→ℂ) (z : ℂ) := μ*z*deriv f z

theorem euler_at_nonzero {μ x c : ℂ} {n : ℤ} {f : ℂ→ℂ} (h : Jet f x n c) :
    Jet (euler μ f) x (n-1) ((μ*x)*(n*c)) := by
  simpa only [zero_add,euler] using!
    (Jet.of_analytic (x:=x) (f:=fun z=>μ*z) (by fun_prop)).mul h.deriv

theorem euler_at_zero {μ c : ℂ} {n : ℤ} {f : ℂ→ℂ} (h : Jet f 0 n c) :
    Jet (euler μ f) 0 n (μ*(n*c)) := by
  have linear : Jet (fun z=>μ*z) 0 1 μ :=
    ⟨fun _=>μ,analyticAt_const,rfl,by simp [mul_comm]⟩
  simpa only [euler,show (1:ℤ)+(n-1)=n by omega] using! linear.mul h.deriv

end ClosedSimilarity.RationalCurvature
