import SolitonClassification.MeromorphicMaximumDisks
import SolitonClassification.MeromorphicMaximumAlgebra
import SolitonClassification.MeromorphicScalarEquation
import SolitonClassification.LowBendingCircles
import SolitonClassification.TangentLawGeometry

noncomputable section
open Complex Set Filter Bornology
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature
open MeromorphicGrowth

/-- Every entire complex solution of the fourth-order similarity curvature
equation is constant. No real slice, periodicity, reality, or restriction
on the two complex coefficients is required. -/
theorem entire_residual_constant {a b : ℂ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (law : ∀z, ordinaryResidual a b f z=0) (x : ℂ) : f x=f 0 := by
  apply hf.apply_eq_apply_of_bounded _ x 0
  refine isBounded_iff_forall_norm_le.mpr ⟨64*(472+2*‖a‖+8*‖b‖),?_⟩
  rintro _ ⟨y,rfl⟩
  obtain ⟨z,h,hp,control,size,est⟩:=exists_cauchy_point hf y
  apply control.trans
  apply maximum_amplitude_bound (a:=a) (b:=b) hp size _ _ _ _ (law z)
  · simpa only [iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,one_mul] using est 1
  · convert est 2 using 1 <;> norm_num [iteratedDeriv_succ, Nat.factorial]
  · convert est 3 using 1 <;> norm_num [iteratedDeriv_succ, Nat.factorial]
  · convert est 4 using 1 <;> norm_num [iteratedDeriv_succ, Nat.factorial]

theorem entire_profile_constant {a b L : ℝ} (p : PeriodicSupportProfile a b L) (lp : 0<L)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (rep : ∀t : ℝ, f (t:ℂ)=(p.k t:ℂ)) :
    ∃K : ℝ, K≠0 ∧ ∀s,p.k s=K := by
  have an (x : ℂ) := hf.analyticAt (z:=x)
  have germ := residual_germ_of_meromorphic_trace p (fun x=>(an x).meromorphicAt)
    (fun t=>an (t:ℂ)) rep
  have globalLaw (x : ℂ) : ordinaryResidual a b f x=0 := by
    have reg : AnalyticAt ℂ (ordinaryResidual a b f) x := by
      unfold ordinaryResidual ordinaryQuadratic ordinaryQuartic
      have af := an x
      fun_prop (disch := assumption)
    have zf : MeromorphicNFAt (fun _ : ℂ=> (0:ℂ)) x := analyticAt_const.meromorphicNFAt
    exact ((reg.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds zf).mp (germ x)).eq_of_nhds
  have flat (t : ℝ) : p.k t=p.k 0 := Complex.ofReal_injective
    ((rep t).symm.trans ((entire_residual_constant hf globalLaw _).trans (by
      simpa only [Complex.ofReal_zero] using rep 0)))
  refine ⟨p.k 0,?_,flat⟩
  intro eq
  have kz (t : ℝ) := (flat t).trans eq
  have pos := p.bending_pos_of_period lp
  simp [PeriodicSupportProfile.bending,kz] at pos

end ClosedSimilarity.MeromorphicCurvature
namespace ClosedSimilarity.ClosedUnitFrenetCurve

/-- The normal law determines a support profile carrying the very same
arclength curvature, for an arbitrary translation of the similarity center. -/
theorem exists_centered_profile_with_curvature (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s,c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s) : ∃p : PeriodicSupportProfile a b c.period,p.k=c.k := by
  by_cases zero : a^2+b^2=0
  · have ha : a=0 := by nlinarith only [zero,sq_nonneg b,sq_nonneg a]
    have hb : b=0 := by nlinarith only [zero,sq_nonneg a,sq_nonneg b]
    exact False.elim (c.no_closed_translator_position_force vx vy (fun s=>by
      simpa [ha,hb] using law s))
  let x₀ := (-a*vx-b*vy)/(a^2+b^2)
  let y₀ := (b*vx-a*vy)/(a^2+b^2)
  let g := c.lowBendingRecenter x₀ y₀
  have shape (s : ℝ) : g.positionForce s= -a*g.normalSupport s-b*g.tangentSupport s := by
    rw [g.positionForce_eq]
    change c.force s=_
    rw [←c.positionForce_eq,law]
    dsimp only [g,lowBendingRecenter,normalSupport,tangentSupport,x₀,y₀]
    field_simp [zero]
    ring
  exact ⟨g.centeredSupportProfile shape,rfl⟩

theorem entire_arclength_curvature_circle (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s,c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (rep : ∀t : ℝ,f (t:ℂ)=(c.k t:ℂ)) :
    ∃(K : ℝ) (O Z : ℂ), K≠0 ∧ Z≠0 ∧ (∀s,c.k s=K) ∧
      ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*I=O+Z*exp (((K*s:ℝ):ℂ)*I) := by
  obtain ⟨p,hk⟩ := c.exists_centered_profile_with_curvature a b vx vy law
  obtain ⟨K,kn,flat⟩ := MeromorphicCurvature.entire_profile_constant p c.period_pos hf
    (fun t=>by rw [hk];exact rep t)
  rw [hk] at flat
  obtain ⟨O,Z,zn,pos⟩ := c.low_bending_circle_parametrization K kn flat
  exact ⟨K,O,Z,kn,zn,flat,pos⟩

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.MeromorphicCurvature.entire_residual_constant
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.entire_arclength_curvature_circle

