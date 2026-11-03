import Lemniscate.PeriodicRotationDomain

/-! The actual dilation mode q^3 is a nonzero H4 eigenvector with eigenvalue -30. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_profile_dilation_eigenmode (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) (hq0 : q 0 = 1) :
    ∃ f : circleH4Domain T,
      (f:CircleL2 T) = circleContinuousL2 T (q^3) ∧
      (f:CircleL2 T) ≠ 0 ∧
      circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f =
        (-30:ℂ) • (f:CircleL2 T) := by
  let f₁ : C(AddCircle T, ℂ) := (3:ℂ) • (q^2*p)
  let f₂ : C(AddCircle T, ℂ) := (3:ℂ) • q-(6:ℂ) • q^5
  let f₃ : C(AddCircle T, ℂ) := (3:ℂ) • p-(30:ℂ) • (q^4*p)
  let f₄ : C(AddCircle T, ℂ) := (-63:ℂ) • q^3+(90:ℂ) • q^7
  have hd₀ : HasCircleDeriv T (q^3) f₁ := by
    intro x
    convert! (hq x).pow 3 using 1
    change 3*((q (x:AddCircle T))^2*p (x:AddCircle T)) =
      3*(q (x:AddCircle T))^(3-1)*p (x:AddCircle T)
    ring
  have hd₁ : HasCircleDeriv T f₁ f₂ := by
    intro x
    convert! (((hq x).pow 2).mul (hp x)).const_mul (3:ℂ) using 1
    change 3*q (x:AddCircle T)-6*(q (x:AddCircle T))^5 =
      3*(2*(q (x:AddCircle T))^(2-1)*p (x:AddCircle T)*p (x:AddCircle T)+
        (q (x:AddCircle T))^2*(-(q (x:AddCircle T))^3))
    linear_combination (-3:ℂ)*q (x:AddCircle T)*(he (x:AddCircle T))
  have hd₂ : HasCircleDeriv T f₂ f₃ := by
    intro x
    convert! ((hq x).const_mul (3:ℂ)).sub (((hq x).pow 5).const_mul (6:ℂ)) using 1
    change 3*p (x:AddCircle T)-30*((q (x:AddCircle T))^4*p (x:AddCircle T)) =
      3*p (x:AddCircle T)-6*(5*(q (x:AddCircle T))^(5-1)*p (x:AddCircle T))
    ring
  have hd₃ : HasCircleDeriv T f₃ f₄ := by
    intro x
    convert! ((hp x).const_mul (3:ℂ)).sub
      ((((hq x).pow 4).mul (hp x)).const_mul (30:ℂ)) using 1
    change -63*(q (x:AddCircle T))^3+90*(q (x:AddCircle T))^7 =
      3*(-(q (x:AddCircle T))^3)-30*(
        4*(q (x:AddCircle T))^(4-1)*p (x:AddCircle T)*p (x:AddCircle T)+
          (q (x:AddCircle T))^4*(-(q (x:AddCircle T))^3))
    linear_combination (60:ℂ)*(q (x:AddCircle T))^3*(he (x:AddCircle T))
  let f : circleH4Domain T :=
    ⟨circleContinuousL2 T (q^3),circle_classical_mem_h4 T _ _ _ _ _ hd₀ hd₁ hd₂ hd₃⟩
  let J : CircleH4Jet T (f:CircleL2 T) := {
    first := circleContinuousL2 T f₁
    second := circleContinuousL2 T f₂
    third := circleContinuousL2 T f₃
    fourth := circleContinuousL2 T f₄
    hfirst := circle_classical_weak_deriv T _ _ hd₀
    hsecond := circle_classical_weak_deriv T _ _ hd₁
    hthird := circle_classical_weak_deriv T _ _ hd₂
    hfourth := circle_classical_weak_deriv T _ _ hd₃ }
  have hjet : circleH4Jet T f = J := circle_h4_jet_unique T _ _ _
  refine ⟨f,rfl,?_,?_⟩
  · intro hz
    have hfun : (q^3 : C(AddCircle T, ℂ)) = 0 := by
      apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
      simpa only [f,circleContinuousL2,map_zero] using hz
    have hzero := congrArg (fun g : C(AddCircle T, ℂ) => g 0) hfun
    change (q 0)^3 = 0 at hzero
    rw [hq0] at hzero
    norm_num at hzero
  · have hclass : (-4:ℂ) • f₄-(45:ℂ) • (q^2*f₂)-
        (75/2:ℂ) • (((2:ℂ) • (q*p))*f₁)-(42:ℂ) • q^3+
        (15/2:ℂ) • ((1-(3:ℂ) • q^4)*q^3) = (-30:ℂ) • q^3 := by
      ext x
      change -4*(-63*(q x)^3+90*(q x)^7)-45*((q x)^2*(3*q x-6*(q x)^5))-
        (75/2)*(2*(q x*p x)*(3*((q x)^2*p x)))-42*(q x)^3+
          (15/2)*((1-3*(q x)^4)*(q x)^3) = -30*(q x)^3
      linear_combination (-225/2:ℂ)*(q x)^3*(he x)
    rw [circle_h4_operator_expanded,hjet]
    change (-4:ℂ) • circleContinuousL2 T f₄-
      (45:ℂ) • circleMultiplyL2 T (q^2) (circleContinuousL2 T f₂)-
      (75/2:ℂ) • circleMultiplyL2 T ((2:ℂ) • (q*p)) (circleContinuousL2 T f₁)-
      (42:ℂ) • circleContinuousL2 T (q^3)+
      (15/2:ℂ) • circleMultiplyL2 T (1-(3:ℂ) • (q^4)) (circleContinuousL2 T (q^3)) =
        (-30:ℂ) • circleContinuousL2 T (q^3)
    simp only [circle_multiply_l2_continuous]
    have hL := congrArg (circleContinuousL2 T) hclass
    simpa only [circleContinuousL2,map_sub,map_add,map_smul] using hL

end Lemniscate
