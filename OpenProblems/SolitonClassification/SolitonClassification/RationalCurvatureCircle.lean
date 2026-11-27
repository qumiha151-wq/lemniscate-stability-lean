import SolitonClassification.RationalProfileBridge
import SolitonClassification.RationalCircleReality
import SolitonClassification.RationalInfinityDegree
import SolitonClassification.RationalOriginRigidity
import SolitonClassification.RationalReduction
import SolitonClassification.TrigCurvatureCircle

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Complex
open scoped Polynomial
namespace ClosedSimilarity.RationalCurvature

/-- The actual signed curvature of a periodic support profile is constant
whenever it is rational in one complex frequency. The representation may
have common polynomial factors, and the frequency is unrestricted. -/
theorem profile_rational_curvature_constant {a b L w : ℝ} (z : PeriodicSupportProfile a b L)
    (hL : 0<L) (A B : ℂ[X]) (safe : ∀s,B.eval (wave w s)≠0)
    (rep : ∀s,quotient A B (wave w s)=(z.k s:ℂ)) : ∃K : ℝ,K≠0 ∧ ∀s,z.k s=K := by
  have flat : ∃K : ℝ,∀s,z.k s=K := by
    by_cases w0 : w=0
    · subst w
      refine ⟨z.k 0,fun s=>Complex.ofReal_injective ?_⟩
      rw [←rep s,←rep 0]
      simp [wave]
    have bn : B≠0 := fun eq=>safe 0 (by simp [eq])
    obtain ⟨U,V,vn,cop,red⟩ := exists_reduced_quotient (A:=A) bn
    have vs (s : ℝ) := (red _ (safe s)).1
    have vr (s : ℝ) := (red _ (safe s)).2.trans (rep s)
    have zero := residual_of_periodicSupportProfile z w0 U V vs vr
    have germ := residual_germ_of_regular vn zero
    have v0 := denominator_at_zero vn cop (germ 0)
    have poles (u : ℂ) (hu : V.eval u=0) := denominator_root_data vn cop hu (germ u)
    have deg : U.degree≤V.degree := by
      by_cases un : U=0
      · simp [un]
      rw [degree_eq_natDegree vn]
      exact degree_le_of_natDegree_le (degree_bound_of_residual un vn zero)
    have phase (s : ℝ) : wave w (s/w)=RationalArclength.unitPhase s := by
      unfold wave RationalArclength.unitPhase
      rw [show w*(s/w)=s by field_simp]
    have imag := RationalArclength.real_origin_of_unit_circle vn v0 deg
      (fun u hu=>(poles u hu).1) (fun u hu=>(poles u hu).2.2)
      (fun s=>phase s ▸ vs (s/w)) (fun s=>by
        change (quotient U V (RationalArclength.unitPhase s)).im=0
        rw [←phase s,vr]
        rfl)
    let K := (quotient U V 0).re
    have real : quotient U V 0=(K:ℂ) := Complex.ext rfl (by simpa [quotient] using imag)
    have constant := constant_quotient_of_real_origin v0 real w0 (z.dilation_pos hL).ne' (germ 0)
    refine ⟨K,fun s=>Complex.ofReal_injective ?_⟩
    rw [←vr s]
    simp [quotient,constant,vs s]
  obtain ⟨K,hk⟩ := flat
  refine ⟨K,?_,hk⟩
  intro k0
  have kz : ∀s,z.k s=0 := fun s=>(hk s).trans k0
  have positive := z.bending_pos_of_period hL
  simp [PeriodicSupportProfile.bending,kz] at positive

end ClosedSimilarity.RationalCurvature
namespace ClosedSimilarity.ClosedUnitFrenetCurve

/-- For every rotation and translation coefficient, a closed free-elastic
similarity profile whose signed arclength curvature is rational in
exp(i w s) parametrizes a circle. Multiple covers are included. -/
theorem rational_exponential_curvature_circle (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s,c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s) (w : ℝ) (A B : ℂ[X])
    (safe : ∀s,B.eval (RationalCurvature.wave w s)≠0)
    (rep : ∀s,RationalCurvature.quotient A B (RationalCurvature.wave w s)=(c.k s:ℂ)) :
    ∃ (K : ℝ) (O Z : ℂ),K≠0 ∧ Z≠0 ∧ (∀s,c.k s=K) ∧
      ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*Complex.I=O+Z*Complex.exp (((K*s:ℝ):ℂ)*Complex.I) := by
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
  let z := g.centeredSupportProfile shape
  obtain ⟨K,kn,hk⟩ := RationalCurvature.profile_rational_curvature_constant z c.period_pos A B safe rep
  obtain ⟨O,Z,zn,p⟩ := c.low_bending_circle_parametrization K kn hk
  exact ⟨K,O,Z,kn,zn,hk,p⟩

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.rational_exponential_curvature_circle
