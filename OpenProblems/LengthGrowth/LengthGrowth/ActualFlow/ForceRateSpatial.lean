import LengthGrowth.ActualFlow.MaterialWeightedRate

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

/-- Weak force-dissipation density after substituting the normal curvature rate. -/
def forceRateWeakDensity (k j l F p q : ℝ) :=
  (2*q+3*k^2*F)*(-q-k^2*F)+2*p*k*F*j-2*k*F^2*l+k*F^3

private def flux (M k j F p : ℝ) := (12*M^2-5*k^2)*F*p-k*F^2*j
private def fluxRate (M k j l F p q : ℝ) :=
  -10*k*j*F*p+(12*M^2-5*k^2)*(p^2+F*q)-j^2*F^2-2*k*F*p*j-k*F^2*l

private theorem square_bound {k j l F p q M S : ℝ} (eq : F=l+k^3/2)
    (hM : |k|≤M) (hS : |j|≤S) :
    forceRateWeakDensity k j l F p q+q^2-fluxRate M k j l F p q ≤
      (36*M^4+8*S^2)*F^2 := by
  have kk := sq_le_sq' (abs_le.mp hM).1 (abs_le.mp hM).2
  have jj := sq_le_sq' (abs_le.mp hS).1 (abs_le.mp hS).2
  have id : (36*M^4+8*S^2)*F^2-
        (forceRateWeakDensity k j l F p q+q^2-fluxRate M k j l F p q)=
      (q+6*M^2*F)^2+7*(k*p-j*F)^2+12*(M^2-k^2)*p^2+
        8*(S^2-j^2)*F^2+(5/2:ℝ)*k^4*F^2 := by
    unfold forceRateWeakDensity fluxRate
    linear_combination -k*F^2*eq
  nlinarith only [id,sq_nonneg (q+6*M^2*F),sq_nonneg (k*p-j*F),
    mul_nonneg (sub_nonneg.mpr kk) (sq_nonneg p),
    mul_nonneg (sub_nonneg.mpr jj) (sq_nonneg F),mul_nonneg (pow_nonneg (sq_nonneg k) 2) (sq_nonneg F)]

/-- The two periodic spatial integrations by parts and the interpolation
estimate on a genuine smooth closed slice, with its actual material density.
Here p and q denote the first and second arclength derivatives of force. -/
theorem force_rate_spatial {γ : ℝ → ℂ} {P M S : ℝ} (hP : 0≤P)
    (smooth : ContDiff ℝ ∞ γ) (reg : ∀u, deriv γ u≠0) (per : Function.Periodic γ P)
    (hM : ∀u∈Icc 0 P, |curvature γ u|≤M) (hS : ∀u∈Icc 0 P, |curvatureGradient γ u|≤S) :
    let k := curvature γ
    let j := curvatureGradient γ
    let l := curvatureSecond γ
    let F := force γ
    let p := arcDerivative γ F
    let q := arcDerivative γ p
    (∫u in 0..P, forceRateWeakDensity (k u) (j u) (l u) (F u) (p u) (q u)*speed γ u)+
      (∫u in 0..P, (q u)^2*speed γ u) ≤ (36*M^4+8*S^2)*materialDissipation γ P := by
  let k := curvature γ
  let j := curvatureGradient γ
  let l := curvatureSecond γ
  let F := force γ
  let p := arcDerivative γ F
  let q := arcDerivative γ p
  let g := speed γ
  let A := fun u => forceRateWeakDensity (k u) (j u) (l u) (F u) (p u) (q u)*g u
  let Y := fun u => q u^2*g u
  let D := fun u => F u^2*g u
  let B := fun u => flux M (k u) (j u) (F u) (p u)
  let b := fun u => fluxRate M (k u) (j u) (l u) (F u) (p u) (q u)*g u
  have sk : ContDiff ℝ ∞ k := curvature_smooth smooth reg
  have sj : ContDiff ℝ ∞ j := curvatureGradient_smooth smooth reg
  have sl : ContDiff ℝ ∞ l := curvatureSecond_smooth smooth reg
  have sF : ContDiff ℝ ∞ F := force_smooth smooth reg
  have sp : ContDiff ℝ ∞ p := arcDerivative_smooth smooth reg sF
  have sq : ContDiff ℝ ∞ q := arcDerivative_smooth smooth reg sp
  have sg : ContDiff ℝ ∞ g := speed_smooth smooth reg
  have ck := sk.continuous
  have cj := sj.continuous
  have cl := sl.continuous
  have cF := sF.continuous
  have cp := sp.continuous
  have cq := sq.continuous
  have cg := sg.continuous
  have bcont : Continuous b := by dsimp only [b,fluxRate]; fun_prop
  have acont : Continuous A := by dsimp only [A,forceRateWeakDensity]; fun_prop
  have ycont : Continuous Y := by dsimp only [Y]; fun_prop
  have dcont : Continuous D := by dsimp only [D]; fun_prop
  have hb (u : ℝ) : HasDerivAt B (b u) u := by
    have dk : HasDerivAt k (g u*j u) u := curvature_hasDerivAt smooth reg u
    have dj : HasDerivAt j (g u*l u) u := curvatureGradient_hasDerivAt smooth reg u
    have dF : HasDerivAt F (g u*p u) u := hasDerivAt_speed_smul_arcDerivative reg (sF.differentiable (by simp)) u
    have dp : HasDerivAt p (g u*q u) u := hasDerivAt_speed_smul_arcDerivative reg (sp.differentiable (by simp)) u
    have lhs := ((((hasDerivAt_const u (12*M^2)).sub ((dk.pow 2).const_mul 5)).mul dF).mul dp)
    have rhs := ((dk.mul (dF.pow 2)).mul dj)
    convert! lhs.sub rhs using 1
    dsimp only [b,fluxRate,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply]
    ring
  have pb : Function.Periodic B P := by
    have pp := arcDerivative_periodic smooth per (sF.differentiable (by simp)) (force_periodic smooth reg per)
    intro u
    simp only [B,k,j,F,p,curvature_periodic smooth reg per u,curvatureGradient_periodic smooth reg per u,
      force_periodic smooth reg per u,pp u]
  have zero := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=P)
    (fun u _ => hb u) (bcont.intervalIntegrable _ _)
  rw [show B P=B 0 by simpa only [zero_add] using pb 0,sub_self] at zero
  have point (u : ℝ) (hu : u∈Icc 0 P) :
      A u+Y u-b u≤(36*M^4+8*S^2)*D u := by
    have e := square_bound (p:=p u) (q:=q u) (show F u=l u+k u^3/2 from rfl)
      (hM u hu) (hS u hu)
    have h := mul_le_mul_of_nonneg_right e (speed_pos reg u).le
    dsimp only [A,Y,b,D,g]
    linarith only [h]
  have integrated := intervalIntegral.integral_mono_on (μ:=volume) hP
    (((acont.add ycont).sub bcont).intervalIntegrable _ _)
    ((dcont.const_mul (36*M^4+8*S^2)).intervalIntegrable _ _) point
  simp only [Pi.add_apply,Pi.sub_apply] at integrated
  have separate := intervalIntegral.integral_sub (μ:=volume) ((acont.add ycont).intervalIntegrable 0 P) (bcont.intervalIntegrable 0 P)
  simp only [Pi.add_apply] at separate
  rw [separate,
    intervalIntegral.integral_add (acont.intervalIntegrable _ _) (ycont.intervalIntegrable _ _),
    zero,sub_zero,intervalIntegral.integral_const_mul] at integrated
  exact integrated

end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.force_rate_spatial

