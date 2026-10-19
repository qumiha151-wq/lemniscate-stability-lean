import Lemniscate.PeriodicH2Energy

/-! Put the H2 energy back into the profile form printed in the paper.
The final theorem applies to arbitrary first and second L2 weak derivatives;
the profile ODE, Fourier formula and period relation remain explicit hypotheses. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_multiply_l2_sub_coefficient (h k : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    circleMultiplyL2 T (h-k) f = circleMultiplyL2 T h f - circleMultiplyL2 T k f := by
  simp only [circleMultiplyL2, map_sub, ContinuousLinearMap.sub_apply]

theorem circle_multiply_l2_smul_coefficient (c : ℂ) (h : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    circleMultiplyL2 T (c • h) f = c • circleMultiplyL2 T h f := by
  simp only [circleMultiplyL2, map_smul, ContinuousLinearMap.smul_apply]

theorem circle_multiply_l2_one (f : CircleL2 T) : circleMultiplyL2 T 1 f = f := by
  apply Lp.ext
  filter_upwards [circle_multiply_l2_ae T 1 f] with x hx
  simpa only [ContinuousMap.one_apply, one_mul] using hx

noncomputable def paperH2Energy (q : C(AddCircle T, ℂ)) (f f₁ f₂ : CircleL2 T) : ℝ :=
  ((-4:ℂ)*inner ℂ f₂ f₂ + 45*inner ℂ f₁ (circleMultiplyL2 T (q^2) f₁) -
    (153/4:ℂ)*inner ℂ f f - (45/4:ℂ)*inner ℂ f (circleMultiplyL2 T (q^4) f)).re

theorem circle_h2_energy_profile (q : C(AddCircle T, ℂ)) (f f₁ f₂ : CircleL2 T) :
    circleH2Energy T (q^2) (1-(3:ℂ) • (q^4)) f f₁ f₂ = paperH2Energy T q f f₁ f₂ := by
  unfold circleH2Energy paperH2Energy
  apply congrArg Complex.re
  rw [circle_multiply_l2_sub_coefficient, circle_multiply_l2_smul_coefficient,
    circle_multiply_l2_one, inner_sub_right, inner_smul_right]
  ring

theorem paper_cosine_weak_energy_dissipative (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (v : CosineSequenceSpace) (u g : CircleL2 T)
    (hfu : HasWeakCircleDeriv T (circleEvenCosineSynthesis T v) u)
    (hug : HasWeakCircleDeriv T u g) :
    paperH2Energy T q (circleEvenCosineSynthesis T v) u g ≤
      -(21/4:ℝ)*‖circleEvenCosineSynthesis T v‖^2 := by
  rw [← circle_h2_energy_profile]
  exact circle_cosine_weak_energy_dissipative T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) hs hc hr v u g hfu hug

end Lemniscate
