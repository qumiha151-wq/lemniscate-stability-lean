import SolitonClassification.LemniscaticLocalGerm
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
open Complex Set Filter Function
open scoped Topology ContDiff
namespace ClosedSimilarity.LemniscaticExtension
set_option backward.isDefEq.respectTransparency false

def OscillatorGerm.pair (g : OscillatorGerm) (z : ℂ) := (g.u z,g.v z)

theorem unique_real_germ {f g h j : ℝ→ℂ} {c : ℂ}
    (lhs : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),HasDerivAt f (c*g t) t ∧ HasDerivAt g (-2*c*f t^3) t)
    (rhs : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),HasDerivAt h (c*j t) t ∧ HasDerivAt j (-2*c*h t^3) t)
    (h0 : f 0=h 0) (h1 : g 0=j 0) :
    ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ), (f t,g t)=(h t,j t) := by
  let A (t : ℝ) := (f t,g t)
  let B (t : ℝ) := (h t,j t)
  let field (p : ℂ × ℂ) := (c*p.2,-2*c*p.1^3)
  have ad : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),HasDerivAt A (field (A t)) t := lhs.mono (fun _ e=>e.1.prodMk e.2)
  have bd : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),HasDerivAt B (field (B t)) t := rhs.mono (fun _ e=>e.1.prodMk e.2)
  have eq : A 0=B 0 := Prod.ext h0 h1
  have sm : ContDiff ℝ 1 field := by unfold field;fun_prop
  obtain ⟨K,V,hv,lc⟩ := (sm.contDiffAt (x:=A 0)).exists_lipschitzOnWith
  have av : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),A t∈V := ad.self_of_nhds.continuousAt hv
  have bv : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),B t∈V := bd.self_of_nhds.continuousAt (eq ▸ hv)
  exact ODE_solution_unique_of_eventually (v:=fun _=>field) (s:=fun _=>V)
    (Eventually.of_forall (fun _=>lc)) (ad.and av) (bd.and bv) eq

theorem real_germ_identity {f g : ℂ→ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (eq : ∀ᶠ (x : ℝ) in 𝓝 (0:ℝ),f (x:ℂ)=g (x:ℂ)) : f=ᶠ[𝓝 0] g := by
  apply (hf.frequently_eq_iff_eventually_eq hg).mp
  have tend : Tendsto (fun x:ℝ=>(x:ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro x hx;simpa using hx
  by_contra! ne
  obtain ⟨x,h1,h2⟩ := ((tend.eventually ne).and (eq.filter_mono nhdsWithin_le_nhds)).exists
  exact h1 h2

theorem OscillatorGerm.real_laws (g : OscillatorGerm) (c : ℂ) :
    ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ), HasDerivAt (fun s:ℝ=>g.u (c*(s:ℂ))) (c*g.v (c*(t:ℂ))) t ∧
      HasDerivAt (fun s:ℝ=>g.v (c*(s:ℂ))) (-2*c*g.u (c*(t:ℂ))^3) t := by
  have lim : Tendsto (fun t:ℝ=>c*(t:ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero,mul_zero,Pi.mul_apply] using! ((continuous_const.mul Complex.continuous_ofReal).continuousAt
      (x:=(0:ℝ)) : ContinuousAt (fun t:ℝ=>c*(t:ℂ)) 0).tendsto
  filter_upwards [lim.eventually g.laws] with t h
  have clk : HasDerivAt (fun z:ℂ=>c*z) c (t:ℂ) := by simpa using (hasDerivAt_id (t:ℂ)).const_mul c
  constructor
  · convert! (h.1.comp ((t:ℂ)) clk).comp_ofReal using 1;ring
  · convert! (h.2.comp ((t:ℂ)) clk).comp_ofReal using 1;ring

theorem OscillatorGerm.quarter_symmetry (g : OscillatorGerm) :
    ∀ᶠ z in 𝓝 0,g.pair (I*z)=(I*g.u z,g.v z) := by
  have hr := g.real_laws 1
  simp only [one_mul,mul_one] at hr
  have other : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),HasDerivAt (fun s:ℝ=>I*g.u (s:ℂ)) (I*g.v (t:ℂ)) t ∧
      HasDerivAt (fun s:ℝ=>g.v (s:ℂ)) (-2*I*(I*g.u (t:ℂ))^3) t := by
    filter_upwards [hr] with t du
    refine ⟨du.1.const_mul I,?_⟩
    convert! du.2 using 1
    linear_combination -2*(g.u (t:ℂ))^3*(I^2-1)*I_sq
  have r := unique_real_germ (g.real_laws I) other (by simp [g.zero]) (by simp)
  have a : AnalyticAt ℂ (fun z:ℂ=>I*z) 0 := by fun_prop
  have au : AnalyticAt ℂ g.u (I*0) := by simpa using g.hu
  have av : AnalyticAt ℂ g.v (I*0) := by simpa using g.hv
  have eu := real_germ_identity (au.comp a) (analyticAt_const.mul g.hu) (r.mono (fun t e=>congrArg Prod.fst e))
  have ev := real_germ_identity (av.comp a) g.hv (r.mono (fun t e=>congrArg Prod.snd e))
  filter_upwards [eu,ev] with z e₁ e₂
  exact Prod.ext e₁ e₂

end ClosedSimilarity.LemniscaticExtension
