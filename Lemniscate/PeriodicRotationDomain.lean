import Lemniscate.PeriodicAdjointFourier

/-! The rotational mode q p lies in the actual periodic H4 domain and is
annihilated by the defined operator. Its four weak derivatives are constructed
from the profile ODE, rather than assumed as extra regularity hypotheses. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

omit [Fact (0 < T)] in
theorem circle_rotation_deriv_one (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    HasCircleDeriv T (q*p) (p^2-q^4) := by
  intro x
  convert! (hq x).mul (hp x) using 1
  change (p (x:AddCircle T))^2-(q (x:AddCircle T))^4 =
    p (x:AddCircle T)*p (x:AddCircle T)+q (x:AddCircle T)*(-(q (x:AddCircle T))^3)
  ring

omit [Fact (0 < T)] in
theorem circle_rotation_deriv_two (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    HasCircleDeriv T (p^2-q^4) ((-6:ℂ) • (q^3*p)) := by
  intro x
  convert! ((hp x).pow 2).sub ((hq x).pow 4) using 1
  change -6*((q (x:AddCircle T))^3*p (x:AddCircle T)) =
    2*(p (x:AddCircle T))^(2-1)*(-(q (x:AddCircle T))^3)-
      4*(q (x:AddCircle T))^(4-1)*p (x:AddCircle T)
  ring

omit [Fact (0 < T)] in
theorem circle_rotation_deriv_three (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    HasCircleDeriv T ((-6:ℂ) • (q^3*p))
      ((-18:ℂ) • (q^2*p^2)+(6:ℂ) • q^6) := by
  intro x
  convert! (((hq x).pow 3).mul (hp x)).const_mul (-6:ℂ) using 1
  change -18*((q (x:AddCircle T))^2*(p (x:AddCircle T))^2)+6*(q (x:AddCircle T))^6 =
    -6*(3*(q (x:AddCircle T))^(3-1)*p (x:AddCircle T)*p (x:AddCircle T)+
      (q (x:AddCircle T))^3*(-(q (x:AddCircle T))^3))
  ring

omit [Fact (0 < T)] in
theorem circle_rotation_deriv_four (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    HasCircleDeriv T ((-18:ℂ) • (q^2*p^2)+(6:ℂ) • q^6)
      ((-36:ℂ) • (q*p^3)+(72:ℂ) • (q^5*p)) := by
  intro x
  have hd := ((((hq x).pow 2).mul ((hp x).pow 2)).const_mul (-18:ℂ)).add
    (((hq x).pow 6).const_mul (6:ℂ))
  convert! hd using 1
  change -36*(q (x:AddCircle T)*(p (x:AddCircle T))^3)+
    72*((q (x:AddCircle T))^5*p (x:AddCircle T)) =
    -18*(2*(q (x:AddCircle T))^(2-1)*p (x:AddCircle T)*(p (x:AddCircle T))^2+
      (q (x:AddCircle T))^2*(2*(p (x:AddCircle T))^(2-1)*(-(q (x:AddCircle T))^3)))+
    6*(6*(q (x:AddCircle T))^(6-1)*p (x:AddCircle T))
  ring

noncomputable def circleRotationJet (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    CircleH4Jet T (circleContinuousL2 T (q*p)) where
  first := circleContinuousL2 T (p^2-q^4)
  second := circleContinuousL2 T ((-6:ℂ) • (q^3*p))
  third := circleContinuousL2 T ((-18:ℂ) • (q^2*p^2)+(6:ℂ) • q^6)
  fourth := circleContinuousL2 T ((-36:ℂ) • (q*p^3)+(72:ℂ) • (q^5*p))
  hfirst := circle_classical_weak_deriv T _ _ (circle_rotation_deriv_one T q p hq hp)
  hsecond := circle_classical_weak_deriv T _ _ (circle_rotation_deriv_two T q p hq hp)
  hthird := circle_classical_weak_deriv T _ _ (circle_rotation_deriv_three T q p hq hp)
  hfourth := circle_classical_weak_deriv T _ _ (circle_rotation_deriv_four T q p hq hp)

theorem circle_rotation_mem_h4 (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    InCircleH4 T (circleContinuousL2 T (q*p)) := by
  let J := circleRotationJet T q p hq hp
  exact ⟨J.first, J.second, J.third, J.fourth, J.hfirst, J.hsecond, J.hthird, J.hfourth⟩

noncomputable def circleRotationH4 (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) : circleH4Domain T :=
  ⟨circleContinuousL2 T (q*p), circle_rotation_mem_h4 T q p hq hp⟩

theorem circle_rotation_h4_jet (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    circleH4Jet T (circleRotationH4 T q p hq hp) = circleRotationJet T q p hq hp :=
  circle_h4_jet_unique T _ _ _

theorem circle_rotation_h4_kernel (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) :
    circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleRotationH4 T q p hq hp) = 0 := by
  have hz : (-4:ℂ) • ((-36:ℂ) • (q*p^3)+(72:ℂ) • (q^5*p)) -
      (45:ℂ) • (q^2*((-6:ℂ) • (q^3*p))) -
      (75/2:ℂ) • (((2:ℂ) • (q*p))*(p^2-q^4)) - (42:ℂ) • (q*p) +
      (15/2:ℂ) • ((1-(3:ℂ) • (q^4))*(q*p)) = 0 := by
    ext x
    change -4*(-36*(q x*(p x)^3)+72*((q x)^5*p x)) -
      45*((q x)^2*(-6*((q x)^3*p x))) - (75/2)*(2*(q x*p x)*((p x)^2-(q x)^4)) -
      42*(q x*p x)+(15/2)*((1-3*(q x)^4)*(q x*p x)) = 0
    linear_combination (69/2:ℂ)*q x*p x*(he x)
  rw [circle_h4_operator_expanded, circle_rotation_h4_jet]
  change (-4:ℂ) • circleContinuousL2 T ((-36:ℂ) • (q*p^3)+(72:ℂ) • (q^5*p)) -
    (45:ℂ) • circleMultiplyL2 T (q^2) (circleContinuousL2 T ((-6:ℂ) • (q^3*p))) -
    (75/2:ℂ) • circleMultiplyL2 T ((2:ℂ) • (q*p)) (circleContinuousL2 T (p^2-q^4)) -
    (42:ℂ) • circleContinuousL2 T (q*p) +
    (15/2:ℂ) • circleMultiplyL2 T (1-(3:ℂ) • (q^4)) (circleContinuousL2 T (q*p)) = 0
  simp only [circle_multiply_l2_continuous]
  have hL := congrArg (circleContinuousL2 T) hz
  simpa only [circleContinuousL2, map_sub, map_add, map_smul, map_zero] using hL

end Lemniscate
