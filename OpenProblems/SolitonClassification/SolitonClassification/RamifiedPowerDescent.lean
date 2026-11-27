import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open Complex Set Filter Function Polynomial
open scoped Topology
namespace ClosedSimilarity.RamifiedCurvature

def rootSection (q : ℕ) (z : ℂ) : ℂ := z ^ ((q:ℂ)⁻¹)

theorem root_pow {q : ℕ} (hq : 0<q) (z : ℂ) : (rootSection q z)^q=z :=
  Complex.cpow_nat_inv_pow z hq.ne'

theorem root_at_zero {q : ℕ} (hq : 0<q) : rootSection q 0=0 :=
  (pow_eq_zero_iff (n:=q) hq.ne').mp (root_pow hq 0)

theorem root_tends_zero {q : ℕ} (hq : 0<q) :
    Tendsto (rootSection q) (𝓝 (0:ℂ)) (𝓝 0) := by
  apply Metric.tendsto_nhds_nhds.mpr
  intro ε ep
  refine ⟨ε^q,pow_pos ep _,?_⟩
  intro z hz
  rw [dist_zero_right] at hz ⊢
  apply lt_of_pow_lt_pow_left₀ q ep.le
  rwa [←norm_pow,root_pow hq]

/-- Holomorphy descends across the finite power map, including the ramification point. -/
theorem analyticAt_of_comp_pow {q : ℕ} (hq : 0<q) {f : ℂ → ℂ}
    (ha : AnalyticAt ℂ (fun w=>f (w^q)) 0) : AnalyticAt ℂ f 0 := by
  let P := fun w : ℂ=>w^q
  have pt := root_tends_zero hq
  have hc := ha.continuousAt.tendsto.comp pt
  have fc : ContinuousAt f 0 := by
    change Tendsto f (𝓝 0) (𝓝 (f 0))
    simpa only [Function.comp_def,root_pow hq,zero_pow hq.ne'] using hc
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ fc
  have anear := pt.eventually ha.eventually_analyticAt
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds anear,eventually_mem_nhdsWithin] with z az nz
  have w0 : rootSection q z≠0 := by
    intro e
    change z≠0 at nz
    apply nz
    rw [←root_pow hq z,e,zero_pow hq.ne']
  have nr : deriv P (rootSection q z)≠0 := by
    change deriv (fun x:ℂ=>x^q) _≠0
    rw [(hasDerivAt_pow q _).deriv]
    exact mul_ne_zero (by exact_mod_cast hq.ne') (pow_ne_zero _ w0)
  have aq : AnalyticAt ℂ P (rootSection q z) := analyticAt_id.pow q
  have hf := (analyticAt_comp_iff_of_deriv_ne_zero (g:=f) aq nr).mp az
  simpa only [P,root_pow hq] using hf.differentiableAt

theorem meromorphicAt_of_comp_pow {q : ℕ} (hq : 0<q) {f : ℂ → ℂ}
    (hm : MeromorphicAt (fun w=>f (w^q)) 0) : MeromorphicAt f 0 := by
  obtain ⟨n,an⟩ := hm
  refine ⟨n,analyticAt_of_comp_pow hq ?_⟩
  have oneq : 1≤q := hq
  have leq : n≤q*n := by simpa only [one_mul] using Nat.mul_le_mul_right n oneq
  have ready : AnalyticAt ℂ (fun w : ℂ=>w^n*f (w^q)) 0 := by simpa using an
  have extra := (analyticAt_id (𝕜:=ℂ) (z:=(0:ℂ))).pow (q*n-n)
  have prod := extra.mul ready
  change AnalyticAt ℂ (fun z : ℂ=>(z^q-0)^n*f (z^q)) 0
  have e : (fun z : ℂ=>(z^q-0)^n*f (z^q)) =
      (fun z : ℂ=>z^(q*n-n)*(z^n*f (z^q))) := by
    funext z
    rw [sub_zero,←pow_mul,←mul_assoc,←pow_add,Nat.sub_add_cancel leq]
  rw [e]
  exact prod

end ClosedSimilarity.RamifiedCurvature

