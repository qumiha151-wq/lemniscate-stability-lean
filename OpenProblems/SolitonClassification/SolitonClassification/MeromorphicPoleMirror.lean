import SolitonClassification.MeromorphicConjugation
import SolitonClassification.MeromorphicPoleExtension
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open Complex ComplexConjugate Set Filter Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

def reflect (x z : ℂ) := 2*x-z
def pull (x : ℂ) (f : ℂ → ℂ) (z : ℂ) := f (reflect x z)
def oddReflect (x : ℂ) (f : ℂ → ℂ) (z : ℂ) := -f (reflect x z)

@[simp] theorem reflect_self (x : ℂ) : reflect x x=x := by dsimp [reflect];ring
@[simp] theorem reflect_twice (x z : ℂ) : reflect x (reflect x z)=z := by dsimp [reflect];ring
theorem reflect_sub (x z : ℂ) : reflect x z-x= -(z-x) := by dsimp [reflect];ring

theorem reflect_punctured (x : ℂ) : Tendsto (reflect x) (𝓝[≠] x) (𝓝[≠] x) := by
  have h : Tendsto (reflect x) (𝓝[≠] x) (𝓝[≠] (reflect x x)) := by
    apply (show Continuous (reflect x) from continuous_const.sub continuous_id).continuousWithinAt.tendsto_nhdsWithin
    intro z hz
    exact fun eq=>hz (sub_right_inj.mp eq)
  simpa only [reflect_self] using h

theorem jet_pull {x c : ℂ} {n : ℤ} {f : ℂ → ℂ} (hf : Jet f x n c) :
    Jet (pull x f) x n ((-1:ℂ)^n*c) := by
  obtain ⟨g,ag,gx,eq⟩ := hf
  have an : AnalyticAt ℂ (reflect x) x := analyticAt_const.sub analyticAt_id
  have atX : AnalyticAt ℂ g (reflect x x) := by simpa using ag
  refine ⟨fun z=>(-1:ℂ)^n*g (reflect x z),analyticAt_const.mul (atX.comp (f:=reflect x) an),
    by simp [gx],?_⟩
  filter_upwards [(reflect_punctured x).eventually eq] with z hz
  change f (reflect x z)=(reflect x z-x)^n*g (reflect x z) at hz
  dsimp only [pull];rw [hz,reflect_sub,neg_eq_neg_one_mul,mul_zpow];ring

theorem jet_odd_simple {x c : ℂ} {f : ℂ → ℂ} (hf : Jet f x (-1) c) :
    Jet (oddReflect x f) x (-1) c := by
  have j:=(jet_pull hf).smul (-1)
  change Jet (fun z=> -f (reflect x z)) x (-1) c
  simpa only [pull,neg_one_mul,zpow_neg_one,inv_neg,inv_one,neg_neg] using j

theorem deriv_pull (x : ℂ) (f : ℂ → ℂ) : deriv (pull x f)=oddReflect x (deriv f) :=
  funext (fun z=>deriv_comp_const_sub f (2*x) z)

theorem deriv_oddReflect (x : ℂ) (f : ℂ → ℂ) : deriv (oddReflect x f)=pull x (deriv f) := by
  funext z
  change deriv (-(pull x f)) z=_
  rw [deriv.neg,deriv_pull]
  simp [oddReflect,pull]

theorem residual_oddReflect (a b x : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    ordinaryResidual a b (oddReflect x f) z=ordinaryResidual a b f (reflect x z) := by
  simp only [ordinaryResidual,ordinaryQuadratic,ordinaryQuartic,deriv_oddReflect,deriv_pull,oddReflect,pull]
  ring

theorem oddReflect_normal {f : ℂ → ℂ} (nf : ∀z,MeromorphicNFAt f z) (x z : ℂ) :
    MeromorphicNFAt (oddReflect x f) z := by
  have act : AnalyticAt ℂ (reflect x) z := analyticAt_const.sub analyticAt_id
  have nonzero : deriv (reflect x) z ≠ 0 := by
    have d:HasDerivAt (reflect x) (0-1) z := (hasDerivAt_const z (2*x)).sub (hasDerivAt_id z)
    rw [d.deriv];norm_num
  have normalPull : MeromorphicNFAt (pull x f) z :=
    (meromorphicNFAt_comp_iff_of_deriv_ne_zero act nonzero).mpr (nf _)
  rcases normalPull with eq|⟨n,g,ga,gn,eq⟩
  · left
    filter_upwards [eq] with w hw
    change pull x f w=0 at hw
    change -(pull x f w)=0
    simp [hw]
  · refine Or.inr ⟨n,-g,ga.neg,by simpa using gn,?_⟩
    filter_upwards [eq] with w hw
    change pull x f w=(w-z)^n*g w at hw
    change -(pull x f w)=(w-z)^n*(-g w)
    rw [hw,mul_neg]

theorem reflected_identity_global {x : ℂ} {f : ℂ → ℂ} (nf : ∀z,MeromorphicNFAt f z)
    (localEq : f =ᶠ[𝓝[≠] x] oddReflect x f) : ∀z, f z= -f (reflect x z) := by
  have mn (z : ℂ):=oddReflect_normal nf x z
  have h0 := meromorphic_identity_plane (f:=fun w=>f w-oddReflect x f w)
    (fun z=>(nf z).meromorphicAt.sub (mn z).meromorphicAt) (x:=x)
    (localEq.mono (fun _ h=>sub_eq_zero.mpr h))
  intro z
  exact (((nf z).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (mn z)).mp
    ((h0 z).mono (fun _ h=>sub_eq_zero.mp h))).eq_of_nhds

theorem period_from_odd_center {x : ℂ} {f : ℂ → ℂ}
    (odd : ∀z,f z= -f (reflect x z)) (realSym : ∀z,f (conj z)=conj (f z))
    (offAxis : x.im≠0) : ∃v : ℂ,v.im≠0 ∧ Periodic f v := by
  have mirror (z : ℂ) : f z= -f (reflect (conj x) z) := by
    have h := congrArg conj (odd (conj z))
    rw [←realSym,conj_conj,map_neg,←realSym] at h
    have two : conj (2:ℂ)=2 := by rw [show (2:ℂ)=1+1 by norm_num,map_add,map_one]
    simpa [reflect,two] using h
  refine ⟨2*(x-conj x),?_,?_⟩
  · simpa [Complex.mul_im] using (show 2*(x.im- -x.im)≠0 by intro e;apply offAxis;linarith)
  · intro z
    rw [show z+2*(x-conj x)=reflect x (reflect (conj x) z) by dsimp [reflect];ring]
    have h:=odd (reflect (conj x) z)
    rw [mirror z]
    linear_combination h

end ClosedSimilarity.MeromorphicCurvature

