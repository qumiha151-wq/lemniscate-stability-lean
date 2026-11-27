import SolitonClassification.TrigSolitonCancellation
import SolitonClassification.TrigFourierCharts
import SolitonClassification.LowBendingCircles
import SolitonClassification.TangentLawGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.TrigCurvature

/-- A nonzero curvature harmonic would force an uncancellable denominator
in the actual fourth-order profile equation. No energy assumption enters. -/
theorem profile_curvature_constant {a b L P : ℝ} (z : PeriodicSupportProfile a b L) (hL : 0<L)
    (hp : 0<P) (S : Finset ℤ) (coeff : ℤ→ℂ)
    (fourier : ∀ s : ℝ,(z.k s:ℂ)=∑ j ∈ S,coeff j*Complex.exp
      (2*(Real.pi:ℂ)*Complex.I*(j:ℂ)*(s:ℂ)/(P:ℂ))) :
    ∃ K : ℝ,K≠0 ∧ ∀s,z.k s=K := by
  let w := 2*Real.pi/P
  have hw : 0<w := by dsimp [w]; positivity
  have flat (s : ℝ) : deriv z.k s=0 := by
    obtain ⟨n,p,rp⟩ := charts_of_finite_fourier hp S coeff fourier s
    obtain ⟨K,all⟩ := chart_constant_of_rep z hL.ne' hw.ne' rp
    have ch : chart s w 0=s := by simp [chart]
    have v := (z.dk (chart s w 0)).comp 0 (chart_hasDerivAt s w 0)
    have constant : HasDerivAt (fun x => z.k (chart s w x)) 0 0 := by
      rw [show (fun x => z.k (chart s w x))=fun _=>K from funext all]
      exact hasDerivAt_const _ _
    have slope := v.unique constant
    simp only [ch,zero_pow (by norm_num : (2:ℕ)≠0),add_zero,div_one] at slope
    rw [(z.dk s).deriv]
    exact (mul_eq_zero.mp slope).resolve_right (div_ne_zero (by norm_num) hw.ne')
  have hk (s : ℝ) := is_const_of_deriv_eq_zero (fun t => (z.dk t).differentiableAt) flat s 0
  refine ⟨z.k 0,?_,hk⟩
  intro h0
  have hz : ∀s,z.k s=0 := fun s => (hk s).trans h0
  have positive := z.bending_pos_of_period hL
  simp [PeriodicSupportProfile.bending,hz] at positive

end ClosedSimilarity.TrigCurvature
namespace ClosedSimilarity.ClosedUnitFrenetCurve

/-- A smooth closed free-elastic similarity profile with any finite Fourier
expansion of its actual signed arclength curvature is a parametrized circle.
The Fourier period need not be the least period of the curvature. -/
theorem finite_fourier_circle (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s, c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s) (P : ℝ) (hp : 0<P) (S : Finset ℤ) (coeff : ℤ→ℂ)
    (fourier : ∀ s : ℝ,(c.k s:ℂ)=∑ j ∈ S,coeff j*Complex.exp
      (2*(Real.pi:ℂ)*Complex.I*(j:ℂ)*(s:ℂ)/(P:ℂ))) :
    ∃ (K : ℝ) (O A : ℂ),K≠0 ∧ A≠0 ∧ (∀s,c.k s=K) ∧
      ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*Complex.I=O+A*Complex.exp (((K*s:ℝ):ℂ)*Complex.I) := by
  by_cases zero : a^2+b^2=0
  · have ha : a=0 := by nlinarith only [zero,sq_nonneg b,sq_nonneg a]
    have hb : b=0 := by nlinarith only [zero,sq_nonneg a,sq_nonneg b]
    exact False.elim (c.no_closed_translator_position_force vx vy (fun s => by
      simpa [ha,hb] using law s))
  · let x₀ := (-a*vx-b*vy)/(a^2+b^2)
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
    obtain ⟨K,kn,hk⟩ := TrigCurvature.profile_curvature_constant z c.period_pos hp S coeff fourier
    obtain ⟨O,A,An,param⟩ := c.low_bending_circle_parametrization K kn hk
    exact ⟨K,O,A,kn,An,hk,param⟩

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.finite_fourier_circle
