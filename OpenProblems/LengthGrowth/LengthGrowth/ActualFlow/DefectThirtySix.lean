import LengthGrowth.ActualFlow.DefectSharpInterpolation
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
namespace LengthGrowth.BendingSublevel

/-- Center the signed curvature moments before estimating the fourth power. -/
theorem necessary_quartic {L μ σ V I₃ I₄ Q : ℝ}
    (hm : 0<μ) (hs : 1≤σ) (variance : V=L*μ^2*(σ^2-1))
    (cubic : 2*(L*μ^3+3*μ*V+I₃)≤(L*μ^2+V)*μ*(1+σ))
    (virial : μ^2*(L*μ^2+V) ≤ -2*Q+L*μ^4+6*μ^2*V+4*μ*I₃+I₄) :
    Q+(5/2-σ-1/(σ+1))*μ^2*V≤I₄/2 := by
  have nz : σ+1 ≠ 0 := by linarith
  have id : μ*((L*μ^2+V)*μ*(1+σ)-2*L*μ^3-6*μ*V) =
      μ^2*V*(σ+1/(σ+1)-5) := by
    rw [variance]; field_simp [nz]; ring
  have upper : 2*μ*I₃ ≤ μ^2*V*(σ+1/(σ+1)-5) := by
    rw [←id]
    linarith only [mul_le_mul_of_nonneg_left cubic hm.le]
  linarith only [virial,upper]

theorem sublevel_constants {d σ μ V : ℝ}
    (hd : d≤36) (hs : 1≤σ) (hm : 0<μ)
    (ratio : 4*Real.pi^2*(σ^2-1)=d) (mass : 2*Real.pi*V=d*μ) :
    69/100 ≤ 5/2-σ-1/(σ+1) ∧ V≤(900/157)*μ := by
  have pi : (157/50:ℝ)<Real.pi := by linarith only [Real.pi_gt_d2]
  have p2 : (157/50:ℝ)^2<Real.pi^2 := by nlinarith only [pi,sq_nonneg (Real.pi-157/50)]
  have ss : 0≤σ^2-1 := by nlinarith only [hs,sq_nonneg (σ-1)]
  have cap : σ≤139/100 := by
    by_contra! bad
    have big : (139/100:ℝ)^2<σ^2 := by nlinarith only [bad,sq_nonneg (σ-139/100)]
    nlinarith only [hd,ratio,big,mul_le_mul_of_nonneg_right p2.le ss]
  constructor
  · have p : 0<σ+1 := by linarith
    have r : 1/(σ+1) ≤ 181/100-σ := by
      apply (div_le_iff₀ p).mpr
      nlinarith only [mul_nonneg (sub_nonneg.mpr cap) (show 0≤139/100+σ-81/100 by linarith)]
    linarith only [r]
  · by_contra! bad
    have vpos : 0<V := by linarith
    nlinarith only [mul_lt_mul_of_pos_right pi vpos,
      mul_le_mul_of_nonneg_right hd hm.le,bad,mass]

/-- A noncircular slice cannot satisfy all the necessary inequalities for a
nonnegative product derivative below the stated threshold. -/
theorem incompatible_nondecreasing_slice {d L μ σ V I₃ I₄ Q : ℝ}
    (hd : d≤36) (hm : 0<μ) (hs : 1≤σ) (hv : 0<V) (hq : 0<Q)
    (ratio : 4*Real.pi^2*(σ^2-1)=d) (mass : 2*Real.pi*V=d*μ)
    (variance : V=L*μ^2*(σ^2-1))
    (cubic : 2*(L*μ^3+3*μ*V+I₃)≤(L*μ^2+V)*μ*(1+σ))
    (virial : μ^2*(L*μ^2+V) ≤ -2*Q+L*μ^4+6*μ^2*V+4*μ*I₃+I₄)
    (interpolation : 3*I₄^2≤V^3*Q) : False := by
  obtain ⟨hc,vcap⟩ := sublevel_constants hd hs hm ratio mass
  have mom := necessary_quartic hm hs variance cubic virial
  have low : 2*(Q+(69/100)*μ^2*V) ≤ I₄ := by
    linarith only [mom,mul_le_mul_of_nonneg_right hc (show 0≤μ^2*V by positivity)]
  have pos : 0≤2*(Q+(69/100)*μ^2*V) := by positivity
  have lowerSquare := sq_le_sq' (by linarith only [low,pos] : -(I₄)≤2*(Q+(69/100)*μ^2*V)) low
  have necessary : 48*(69/100)*μ^2*(V*Q) ≤ V^2*(V*Q) := by
    nlinarith only [interpolation,lowerSquare,sq_nonneg (Q-(69/100)*μ^2*V)]
  have gap := le_of_mul_le_mul_right necessary (mul_pos hv hq)
  have v2 := sq_le_sq' (by linarith : -((900/157)*μ)≤V) vcap
  nlinarith only [gap,v2,sq_pos_of_pos hm]

end LengthGrowth.BendingSublevel

namespace LengthGrowth.ActualFlow.ForwardImmersion

/-- The curvature-moment barrier only needs to supply inward derivatives on
the top level to give the fourth-root estimate on the actual material flow. -/
theorem quarter_length_of_bending_sublevel_boundary (c : ForwardImmersion) (hf : c.IsNormalFEF)
    (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36)
    (inward : ∀s, 0≤s → 2*c.normalizedProduct s=4*Real.pi^2+36 →
      ∃d : ℝ, d<0 ∧ HasDerivWithinAt (fun t => 2*c.normalizedProduct t) d (Set.Ici 0) s) :
    c.HasQuarterLengthBound := by
  apply c.quarter_length_of_bounded_absoluteCurvature hf
  apply c.bounded_absoluteCurvature_of_bounded_energyLength
  refine ⟨(4*Real.pi^2+36)/2,fun t ht => ?_⟩
  have h := LengthGrowth.DefectFour.sublevel_forward (U:=fun s => 2*c.normalizedProduct s)
    ht (continuousOn_const.mul c.normalizedProduct_continuousOn) initial inward
  change c.normalizedProduct t≤_
  linarith

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.BendingSublevel.incompatible_nondecreasing_slice
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_bending_sublevel_boundary
