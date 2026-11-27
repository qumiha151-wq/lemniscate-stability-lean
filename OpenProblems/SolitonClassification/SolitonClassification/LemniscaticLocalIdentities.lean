import SolitonClassification.LemniscaticGermSymmetry
import SolitonClassification.LemniscaticReal

noncomputable section
open Complex Set Filter
open scoped Topology
namespace ClosedSimilarity.LemniscaticExtension

theorem OscillatorGerm.real_match (g : OscillatorGerm) :
    ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),g.pair (t:ℂ)=realPair t := by
  have u := g.real_laws 1
  simp only [one_mul,mul_one] at u
  have other (t : ℝ) : HasDerivAt (fun s=>(realU s:ℂ)) ((1:ℂ)*(realV t:ℂ)) t ∧
      HasDerivAt (fun s=>(realV s:ℂ)) (-2*(1:ℂ)*(realU t:ℂ)^3) t := by
    constructor
    · simpa only [one_mul] using (realU_deriv t).ofReal_comp
    · simpa only [mul_one,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,
        Complex.ofReal_pow] using (realV_deriv t).ofReal_comp
  exact unique_real_germ (c:=1) (by simpa only [one_mul,mul_one] using u)
    (Eventually.of_forall other) (by simp [g.zero]) (by simp [g.one])

theorem OscillatorGerm.double_local (g : OscillatorGerm) :
    ∀ᶠ z in 𝓝 0,double (g.pair (z/2))=g.pair z := by
  have cmp : Tendsto (fun t:ℝ=>t/2) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_id.div_const 2).continuousAt (x:=(0:ℝ))).tendsto
  have r : ∀ᶠ (t : ℝ) in 𝓝 (0:ℝ),double (g.pair ((t:ℂ)/2))=g.pair (t:ℂ) := by
    filter_upwards [g.real_match,cmp.eventually g.real_match] with t a b
    rw [show (t:ℂ)/2=((t/2:ℝ):ℂ) by push_cast;rfl,b,a,real_double]
    congr 1
    ring
  have hc : AnalyticAt ℂ (fun z:ℂ=>z/2) 0 := by fun_prop
  have hu : AnalyticAt ℂ (fun z:ℂ=>g.u (z/2)) 0 := by
    apply AnalyticAt.comp _ hc
    simpa using g.hu
  have hv : AnalyticAt ℂ (fun z:ℂ=>g.v (z/2)) 0 := by
    apply AnalyticAt.comp _ hc
    simpa using g.hv
  have dn : 1+g.u ((0:ℂ)/2)^4≠0 := by simp [g.zero]
  have d1 : AnalyticAt ℂ (fun z=>(double (g.pair (z/2))).1) 0 :=
    (((analyticAt_const.mul hu).mul hv).div (analyticAt_const.add (hu.pow 4)) dn)
  have d2 : AnalyticAt ℂ (fun z=>(double (g.pair (z/2))).2) 0 :=
    (((analyticAt_const.sub (analyticAt_const.mul (hu.pow 4))).add (hu.pow 8)).div
      ((analyticAt_const.add (hu.pow 4)).pow 2) (pow_ne_zero 2 dn))
  have e1 := real_germ_identity d1 g.hu (r.mono (fun t e=>congrArg Prod.fst e))
  have e2 := real_germ_identity d2 g.hv (r.mono (fun t e=>congrArg Prod.snd e))
  filter_upwards [e1,e2] with z x y
  exact Prod.ext x y

end ClosedSimilarity.LemniscaticExtension
