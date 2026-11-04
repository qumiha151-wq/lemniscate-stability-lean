import Lemniscate.PeriodicParabolicUniqueness
import Lemniscate.PeriodicParabolicSolvability
import Lemniscate.PeriodicParabolicNormedSpace
import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual principal parabolic data map is a Banach-space isomorphism.
Its inverse is the unique solution furnished by maximal-L2 existence. The
quantitative bound is transferred from that solution, rather than assumed
for an abstract inverse. The zero-initial inverse is the same inverse
restricted to data of the form (0,F).
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

private theorem additive_data_bijective
    {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    (initial : E →+ F) (A : E →+ G)
    (hzero : ∀ U : E, initial U = 0 → A U = 0 → U = 0)
    (q : F → G → E → Prop)
    (hsol : ∀ x : F, ∀ y : G, ∃ U : E, initial U = x ∧ A U = y ∧ q x y U) :
    Function.Bijective (fun U : E => (initial U,A U)) := by
  constructor
  · intro U V hUV
    have hi : initial U = initial V := congrArg Prod.fst hUV
    have ha : A U = A V := congrArg Prod.snd hUV
    apply sub_eq_zero.mp
    apply hzero (U-V)
    · rw [map_sub,hi,sub_self]
    · rw [map_sub,ha,sub_self]
  · rintro ⟨x,y⟩
    obtain ⟨U,hi,ha,_⟩ := hsol x y
    exact ⟨U,Prod.ext hi ha⟩

private theorem inverse_value_bound_of_solvability
    {E F G : Type*} (e : E ≃ F × G) (initial : E → F) (A : E → G)
    (he : ∀ U : E, e U = (initial U,A U)) (p : E → ℝ) (b : F → G → ℝ)
    (hsol : ∀ x : F, ∀ y : G,
      ∃ U : E, initial U = x ∧ A U = y ∧ p U ≤ b x y)
    (x : F) (y : G) : p (e.symm (x,y)) ≤ b x y := by
  obtain ⟨U,hi,ha,hbound⟩ := hsol x y
  have hdata : e U = (x,y) := (he U).trans (Prod.ext hi ha)
  have heval := congrArg e.symm hdata
  have hU : e.symm (x,y) = U := heval.symm.trans (e.symm_apply_apply U)
  exact (congrArg p hU).le.trans hbound

variable (T : ℝ) [Fact (0 < T)]

/-- The actual initial value and principal equation of a parabolic solution. -/
def circleParabolicDataMap (τ : ℝ) :
    CircleParabolicSpace T τ →L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T) :=
  (circleParabolicInitialValue T τ).prod (circleParabolicPrincipalRHS T τ)

set_option maxHeartbeats 600000 in
private theorem circle_parabolic_data_map_bijective (τ : ℝ) (hτ : 0 < τ) :
    Function.Bijective (circleParabolicDataMap T τ) := by
  simpa only [circleParabolicDataMap,ContinuousLinearMap.prod_apply] using!
    additive_data_bijective
      (E := ↥(CircleParabolicSpace T τ)) (F := ↥(CircleSobolevSpace T 2))
      (G := ↥(CircleTimeL2 T))
      (circleParabolicInitialValue T τ).toLinearMap.toAddMonoidHom
      (circleParabolicPrincipalRHS T τ).toLinearMap.toAddMonoidHom
      (circle_parabolic_principal_eq_zero T τ)
      (fun u0 F U => ‖U‖^2 ≤ 40*((1+τ)*‖F‖^2+(1+τ⁻¹)*‖u0‖^2))
      (circle_parabolic_principal_solvability T τ hτ)

set_option maxHeartbeats 600000 in
/-- The data-to-solution isomorphism for the actual principal equation. -/
def circleParabolicDataEquiv (τ : ℝ) (hτ : 0 < τ) :
    CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T) := by
  simpa only using! ContinuousLinearEquiv.ofBijective
    (𝕜 := ℂ) (𝕜' := ℂ) (σ := RingHom.id ℂ) (σ' := RingHom.id ℂ)
    (E := ↥(CircleParabolicSpace T τ))
    (F := ↥(CircleSobolevSpace T 2) × ↥(CircleTimeL2 T)) (circleParabolicDataMap T τ)
    (LinearMap.ker_eq_bot.mpr (circle_parabolic_data_map_bijective T τ hτ).1)
    (LinearMap.range_eq_top.mpr (circle_parabolic_data_map_bijective T τ hτ).2)

@[simp] theorem circle_parabolic_data_equiv_apply (τ : ℝ) (hτ : 0 < τ)
    (U : CircleParabolicSpace T τ) :
    circleParabolicDataEquiv T τ hτ U =
      (circleParabolicInitialValue T τ U,circleParabolicPrincipalRHS T τ U) := rfl

@[simp] theorem circle_parabolic_inverse_initial (τ : ℝ) (hτ : 0 < τ)
    (u0 : CircleSobolevSpace T 2) (F : CircleTimeL2 T) :
    circleParabolicInitialValue T τ ((circleParabolicDataEquiv T τ hτ).symm (u0,F)) = u0 := by
  let U : CircleParabolicSpace T τ := (circleParabolicDataEquiv T τ hτ).symm (u0,F)
  have hpair : (circleParabolicInitialValue T τ U,circleParabolicPrincipalRHS T τ U) = (u0,F) :=
    (circle_parabolic_data_equiv_apply T τ hτ U).symm.trans
      ((circleParabolicDataEquiv T τ hτ).apply_symm_apply (u0,F))
  exact congrArg (fun z : CircleSobolevSpace T 2 × CircleTimeL2 T => z.1) hpair

@[simp] theorem circle_parabolic_inverse_rhs (τ : ℝ) (hτ : 0 < τ)
    (u0 : CircleSobolevSpace T 2) (F : CircleTimeL2 T) :
    circleParabolicPrincipalRHS T τ ((circleParabolicDataEquiv T τ hτ).symm (u0,F)) = F := by
  let U : CircleParabolicSpace T τ := (circleParabolicDataEquiv T τ hτ).symm (u0,F)
  have hpair : (circleParabolicInitialValue T τ U,circleParabolicPrincipalRHS T τ U) = (u0,F) :=
    (circle_parabolic_data_equiv_apply T τ hτ U).symm.trans
      ((circleParabolicDataEquiv T τ hτ).apply_symm_apply (u0,F))
  exact congrArg (fun z : CircleSobolevSpace T 2 × CircleTimeL2 T => z.2) hpair

set_option maxHeartbeats 600000 in
/-- The original maximal-L2 square-norm estimate for the actual inverse. -/
theorem circle_parabolic_inverse_bound (τ : ℝ) (hτ : 0 < τ)
    (u0 : CircleSobolevSpace T 2) (F : CircleTimeL2 T) :
    ‖(circleParabolicDataEquiv T τ hτ).symm (u0,F)‖^2 ≤
      40*((1+τ)*‖F‖^2+(1+τ⁻¹)*‖u0‖^2) := by
  simpa only using! inverse_value_bound_of_solvability
    (E := ↥(CircleParabolicSpace T τ)) (F := ↥(CircleSobolevSpace T 2))
    (G := ↥(CircleTimeL2 T)) (circleParabolicDataEquiv T τ hτ).toLinearEquiv.toEquiv
    (circleParabolicInitialValue T τ) (circleParabolicPrincipalRHS T τ)
    (circle_parabolic_data_equiv_apply T τ hτ)
    (fun U : CircleParabolicSpace T τ => ‖U‖^2)
    (fun u0 F => 40*((1+τ)*‖F‖^2+(1+τ⁻¹)*‖u0‖^2))
    (circle_parabolic_principal_solvability T τ hτ) u0 F

/-- The principal forcing inverse with zero initial value, obtained from
the same data isomorphism by the continuous linear inclusion F ↦ (0,F). -/
def circleParabolicZeroInitialInverse (τ : ℝ) (hτ : 0 < τ) :
    CircleTimeL2 T →L[ℂ] CircleParabolicSpace T τ :=
  (circleParabolicDataEquiv T τ hτ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ (CircleSobolevSpace T 2) (CircleTimeL2 T))

@[simp] theorem circle_parabolic_zero_initial_inverse_apply (τ : ℝ) (hτ : 0 < τ)
    (F : CircleTimeL2 T) :
    circleParabolicZeroInitialInverse T τ hτ F =
      (circleParabolicDataEquiv T τ hτ).symm (0,F) := rfl

set_option maxHeartbeats 600000 in
@[simp] theorem circle_parabolic_zero_initial_inverse_initial (τ : ℝ) (hτ : 0 < τ)
    (F : CircleTimeL2 T) :
    circleParabolicInitialValue T τ (circleParabolicZeroInitialInverse T τ hτ F) = 0 := by
  have heval := congrArg (circleParabolicInitialValue T τ)
    (circle_parabolic_zero_initial_inverse_apply T τ hτ F)
  exact heval.trans (circle_parabolic_inverse_initial T τ hτ 0 F)

set_option maxHeartbeats 600000 in
@[simp] theorem circle_parabolic_zero_initial_inverse_rhs (τ : ℝ) (hτ : 0 < τ)
    (F : CircleTimeL2 T) :
    circleParabolicPrincipalRHS T τ (circleParabolicZeroInitialInverse T τ hτ F) = F := by
  have heval := congrArg (circleParabolicPrincipalRHS T τ)
    (circle_parabolic_zero_initial_inverse_apply T τ hτ F)
  exact heval.trans (circle_parabolic_inverse_rhs T τ hτ 0 F)

private theorem parabolic_zero_inverse_real_bound
    (a b τ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ1 : τ ≤ 1)
    (h : a^2 ≤ 40*((1+τ)*b^2)) : a ≤ 10*b := by
  have hscale : (1+τ)*b^2 ≤ 2*b^2 :=
    mul_le_mul_of_nonneg_right (by linarith : 1+τ ≤ 2) (sq_nonneg b)
  have h80 : a^2 ≤ 40*(2*b^2) :=
    h.trans (mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 40))
  have hsq : a^2 ≤ (10*b)^2 := by nlinarith only [h80,sq_nonneg b]
  exact (sq_le_sq₀ ha (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hb)).mp hsq

set_option maxHeartbeats 600000 in
/-- The zero-initial forcing inverse has a time-independent bound for 0<τ≤1. -/
theorem circle_parabolic_zero_initial_inverse_bound
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (F : CircleTimeL2 T) :
    ‖circleParabolicZeroInitialInverse T τ hτ F‖ ≤ 10*‖F‖ := by
  have hs : ‖(circleParabolicDataEquiv T τ hτ).symm (0,F)‖^2 ≤ 40*((1+τ)*‖F‖^2) := by
    simpa only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,add_zero] using!
      circle_parabolic_inverse_bound T τ hτ (0 : CircleSobolevSpace T 2) F
  have hn : ‖circleParabolicZeroInitialInverse T τ hτ F‖^2 =
      ‖(circleParabolicDataEquiv T τ hτ).symm (0,F)‖^2 :=
    congrArg (fun W : CircleParabolicSpace T τ => ‖W‖^2)
      (circle_parabolic_zero_initial_inverse_apply T τ hτ F)
  exact parabolic_zero_inverse_real_bound ‖circleParabolicZeroInitialInverse T τ hτ F‖ ‖F‖ τ
    (norm_nonneg _) (norm_nonneg F) hτ1 (hn.le.trans hs)

end Lemniscate
