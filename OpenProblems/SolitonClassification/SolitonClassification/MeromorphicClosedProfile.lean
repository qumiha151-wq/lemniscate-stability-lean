import SolitonClassification.MeromorphicPoleParity
import SolitonClassification.MeromorphicPoleIndicial
import SolitonClassification.EntireCurvatureRigidity
import SolitonClassification.EllipticArclengthClassification
import SolitonClassification.LemniscaticElliptic

noncomputable section
open Complex Filter Set Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

/-- A single-valued continuation of the actual curvature to the full complex
arclength plane. No growth or nonreal period is part of the definition. -/
def GlobalMeromorphicTrace (k : ℝ → ℝ) : Prop :=
  ∃f : ℂ → ℂ, Meromorphic f ∧ (∀s : ℝ,AnalyticAt ℂ f (s:ℂ)) ∧ ∀s : ℝ,f (s:ℂ)=(k s:ℂ)

theorem GlobalMeromorphicTrace.normalized {k : ℝ → ℝ} (h : GlobalMeromorphicTrace k) :
    ∃f : ℂ → ℂ,(∀x,MeromorphicNFAt f x) ∧ (∀s : ℝ,AnalyticAt ℂ f (s:ℂ)) ∧
      ∀s : ℝ,f (s:ℂ)=(k s:ℂ) := by
  obtain ⟨f,mer,reg,rep⟩:=h
  let g := toMeromorphicNFOn f univ
  have normal (x : ℂ) : MeromorphicNFAt g x := meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ x)
  have germs (t : ℝ) : g =ᶠ[𝓝 (t:ℂ)] f :=
    ((normal _).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (reg t).meromorphicNFAt).mp
      (mer.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ (t:ℂ)))
  exact ⟨g,normal,fun t=>(analyticAt_congr (germs t)).mpr (reg t),
    fun t=>(germs t).eq_of_nhds.trans (rep t)⟩

theorem pole_is_odd_center {a b : ℝ} (ap : 0<a) {f : ℂ → ℂ} (nf : ∀z,MeromorphicNFAt f z)
    {x : ℂ} (sing : ¬AnalyticAt ℂ f x)
    (law : ordinaryResidual a b f =ᶠ[𝓝[≠] x] fun _=>0) : ∀z,f z= -f (reflect x z) := by
  have neg : meromorphicOrderAt f x<0 :=
    lt_of_not_ge (fun ge=>sing ((nf x).meromorphicOrderAt_nonneg_iff_analyticAt.mp ge))
  lift meromorphicOrderAt f x to ℤ using LT.lt.ne_top neg with n hn
  obtain ⟨_,c,cs,jet,⟨R,ar,expan⟩,_⟩ := pole_expansion ap (nf x).meromorphicAt hn.symm
    (WithTop.coe_lt_zero.mp neg) law
  have rg : ordinaryResidual a b (oddReflect x f) =ᶠ[𝓝[≠] x] fun _=>0 := by
    filter_upwards [(reflect_punctured x).eventually law] with z hz
    exact (residual_oddReflect _ _ _ _ _).trans hz
  apply reflected_identity_global nf
  apply reflection_of_fifth_uniqueness (regular_difference_of_remainder ar expan)
  intro m d nonneg dn j
  exact pole_difference_order_five jet (jet_odd_simple jet) cs j dn nonneg law rg

/-- A meromorphic continuation of a physically closed similarity profile is
constant or necessarily acquires a nonreal period; the latter forces the
lemniscatic oscillator on the real axis. -/
theorem meromorphic_curvature_dichotomy {a b L : ℝ} (p : PeriodicSupportProfile a b L) (hL : 0<L)
    (extn : GlobalMeromorphicTrace p.k) :
    (∃K : ℝ,K≠0 ∧ ∀t,p.k t=K) ∨ (∀t,deriv (deriv p.k) t+2/9*p.k t^3=0) := by
  obtain ⟨f,nf,reg,rep⟩:=extn.normalized
  by_cases all : ∀x,AnalyticAt ℂ f x
  · exact Or.inl (entire_profile_constant p hL (fun x=>(all x).differentiableAt) rep)
  obtain ⟨x,sing⟩ := not_forall.mp all
  have im : x.im≠0 := by
    intro zero
    have realX : (x.re:ℂ)=x := Complex.ext rfl (by simp [zero])
    exact sing (realX ▸ reg x.re)
  have law := residual_germ_of_meromorphic_trace p (fun z=>(nf z).meromorphicAt) reg rep x
  have odd:=pole_is_odd_center (p.dilation_pos hL) nf sing law
  obtain ⟨v,vn,per⟩:=period_from_odd_center odd (normal_conj_symmetry nf rep) im
  exact periodic_elliptic_curvature p hL ⟨f,nf,reg,rep,v,vn,per⟩

theorem meromorphic_curvature_iff {a b L : ℝ} (p : PeriodicSupportProfile a b L) (hL : 0<L) :
    GlobalMeromorphicTrace p.k ↔
    (∃K : ℝ,K≠0 ∧ ∀t,p.k t=K) ∨ (∀t,deriv (deriv p.k) t+2/9*p.k t^3=0) := by
  refine ⟨meromorphic_curvature_dichotomy p hL,?_⟩
  rintro (⟨K,_,hk⟩|osc)
  · exact ⟨fun _=>(K:ℂ),fun _=>analyticAt_const.meromorphicAt,fun _=>analyticAt_const,fun s=>by rw [hk]⟩
  · have dk : deriv p.k=p.v := funext (fun s=>(p.dk s).deriv)
    have dv (s : ℝ) : HasDerivAt p.v (-2/9*p.k s^3) s := by
      have e:=osc s
      rw [dk,(p.dv s).deriv] at e
      exact (p.dv s).congr_deriv (by linarith only [e])
    obtain ⟨e⟩:=LemniscaticExtension.profile_oscillator_elliptic p hL dv
    exact ⟨e.extension,fun x=>(e.normal x).meromorphicAt,e.analytic_real,e.restrict_real⟩

end ClosedSimilarity.MeromorphicCurvature
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open MeromorphicCurvature

/-- The complete classification for single-valued meromorphic signed
arclength curvature, with arbitrary growth, poles, and similarity generator. -/
theorem meromorphic_curvature_circle_or_bernoulli (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s,c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s) (extn : GlobalMeromorphicTrace c.k) :
    (∃(K : ℝ) (O Z : ℂ), K≠0 ∧ Z≠0 ∧ (∀s,c.k s=K) ∧
      ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*I=O+Z*exp (((K*s:ℝ):ℂ)*I)) ∨
      (b=0 ∧ BernoulliGeometry.IsBernoulliCover c a vx vy) := by
  obtain ⟨p,hk⟩:=c.exists_centered_profile_with_curvature a b vx vy law
  have extp : GlobalMeromorphicTrace p.k := hk ▸ extn
  have sol:=meromorphic_curvature_dichotomy p c.period_pos extp
  rw [hk] at sol
  obtain ⟨K,kn,flat⟩|osc:=sol
  · obtain ⟨O,Z,zn,pos⟩:=c.low_bending_circle_parametrization K kn flat
    exact Or.inl ⟨K,O,Z,kn,zn,flat,pos⟩
  · exact Or.inr (c.bernoulli_of_cubic_oscillator a b vx vy law osc)

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.MeromorphicCurvature.meromorphic_curvature_iff
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.meromorphic_curvature_circle_or_bernoulli

