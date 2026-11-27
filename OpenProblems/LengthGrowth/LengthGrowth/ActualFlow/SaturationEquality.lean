import LengthGrowth.ActualFlow.SaturationAnnulus

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- On the sharp residual level, the centered radius is constant, its value is
the single-traversal radius, and the energy–length product is minimal. -/
theorem growthResidual_equality_geometry
    (sharp : (∫s in 0..c.period,c.growthResidual s^2)*c.period^3=Real.pi^2*c.energy^2) :
    (∀s, ‖c.curve s-c.arclengthCentroid‖=c.period/(2*Real.pi)) ∧
    (∀s,c.radialTangentSupport s=0) ∧ c.energy*c.period=2*Real.pi^2 := by
  let r := ∫s in 0..c.period,c.growthResidual s^2
  let y := fun s => c.curve s-c.arclengthCentroid
  let R := ‖y 0‖
  have lp := c.period_pos
  have ep := c.energy_pos
  have pp := Real.pi_pos
  have rp : 0<r := by
    have pos : 0<Real.pi^2*c.energy^2 := by positivity
    rw [←sharp] at pos
    exact pos_of_mul_pos_left pos (pow_nonneg lp.le 3)
  have rad (s : ℝ) : ‖y s‖^2=R^2 := by
    obtain ⟨v,hv,ve⟩ := c.periodic_representative c.curve_periodic s
    have h := c.growthResidual_centroid_annulus hv (show (0:ℝ)∈Icc 0 c.period from ⟨le_rfl,lp.le⟩)
    change Real.pi^2*r*(‖c.curve v-c.arclengthCentroid‖^2-R^2)^2 ≤ _ at h
    have ez : r*c.period^4-Real.pi^2*c.energy^2*c.period=0 := by
      change r*c.period^3=Real.pi^2*c.energy^2 at sharp
      nlinarith only [congrArg (·*c.period) sharp]
    rw [ez] at h
    have z0 : (‖c.curve v-c.arclengthCentroid‖^2-R^2)^2 ≤ 0 := by
      by_contra! pos
      exact (not_lt_of_ge h) (mul_pos (mul_pos (sq_pos_of_pos pp) rp) pos)
    rw [ve] at z0
    change ‖c.curve s-c.arclengthCentroid‖^2=R^2
    nlinarith only [z0]
  have dsrad (s : ℝ) : HasDerivAt (fun w => ‖y w‖^2) (2*c.radialTangentSupport s) s := by
    have d := (c.curve_deriv s).sub_const c.arclengthCentroid
    have v := d.inner ℝ d
    simp only [real_inner_self_eq_norm_sq] at v
    apply v.congr_deriv
    change _=2*inner ℝ (c.tangent s) (c.curve s-c.arclengthCentroid)
    linarith only [real_inner_comm (c.curve s-c.arclengthCentroid) (c.tangent s)]
  have zt (s : ℝ) : c.radialTangentSupport s=0 := by
    have const := funext rad
    have d := dsrad s
    rw [const] at d
    linarith only [d.unique (hasDerivAt_const s (R^2))]
  have normp (s : ℝ) : c.similaritySupport c.arclengthCentroid 0 s^2=R^2 := by
    have py := c.centered_support_pythagoras s
    rw [zt s,zero_pow (by decide : (2:ℕ)≠0),zero_add] at py
    exact py.trans (rad s)
  have rhi := c.centered_support_moment_le
  have rlo := c.growthResidual_support_cost c.arclengthCentroid 0
  simp only [normp,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at rhi rlo
  have exactR : (2*Real.pi)^2 * (c.period*R^2)=c.period^3 := by
    apply le_antisymm rhi
    apply (mul_le_mul_iff_left₀ rp).mp
    change r*c.period^3=Real.pi^2*c.energy^2 at sharp
    change (c.energy/2)^2≤r*(c.period*R^2) at rlo
    nlinarith only [sharp,mul_le_mul_of_nonneg_left rlo (sq_nonneg (2*Real.pi))]
  have radiusId : (2*Real.pi*R)^2=c.period^2 := by
    apply (mul_left_cancel₀ lp.ne' : c.period*_ = c.period*_ → _)
    nlinarith only [exactR]
  have Rn : 0≤R := norm_nonneg _
  have radius : R=c.period/(2*Real.pi) := by
    apply (eq_div_iff (by positivity : (2*Real.pi)≠0)).mpr
    have z := (sq_eq_sq₀ (mul_nonneg (by positivity : 0≤2*Real.pi) Rn) lp.le).mp radiusId
    linarith
  have dk (s : ℝ) : HasDerivAt c.radialTangentSupport
      (c.curvature s*c.similaritySupport c.arclengthCentroid 0 s+1) s := by
    apply ((c.tangent_deriv s).inner ℝ ((c.curve_deriv s).sub_const c.arclengthCentroid)).congr_deriv
    rw [←Complex.real_smul,real_inner_smul_left,real_inner_self_eq_norm_sq,c.tangent_unit]
    simp [similaritySupport,normal,add_comm]
  have ksq (s : ℝ) : c.curvature s^2*R^2=1 := by
    have dz := dk s
    rw [show c.radialTangentSupport=fun _ => 0 by funext x; exact zt x] at dz
    have kneg : c.curvature s*c.similaritySupport c.arclengthCentroid 0 s= -1 := by
      linarith only [dz.unique (hasDerivAt_const s (0:ℝ))]
    have eq := congrArg (fun x:ℝ => x^2) kneg
    simpa only [mul_pow,normp,neg_sq,one_pow] using eq
  have hi := congrArg (fun f : ℝ→ℝ => ∫x in 0..c.period,f x) (funext ksq)
  change (∫x in 0..c.period,c.curvature x^2*R^2)=(∫x in 0..c.period,(1:ℝ)) at hi
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hi
  have kk : (∫x in 0..c.period,c.curvature x^2)=2*c.energy := by unfold energy; ring
  rw [kk,radius] at hi
  field_simp [Real.pi_ne_zero] at hi
  refine ⟨fun s => ?_,zt,?_⟩
  · rw [←radius]
    exact (sq_eq_sq₀ (norm_nonneg _) Rn).mp (rad s)
  · exact hi
end LengthGrowth.ClosedFrenetCurve

#print axioms LengthGrowth.ClosedFrenetCurve.growthResidual_equality_geometry
