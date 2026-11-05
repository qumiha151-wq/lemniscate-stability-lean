import Lemniscate.PeriodicCenteredBlochLinear
import Lemniscate.PeriodicReducedForm

/-! Exact congruence after multiplying the center coordinate by alpha.
There is no division by alpha, so the identity also holds at alpha=0. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleCenterDilation (α : ℝ) (f : circleH4Domain T) : circleH4Domain T :=
  (α:ℂ) • circleFixedProjectionH4 T f+(f-circleFixedProjectionH4 T f)

theorem circle_center_dilation_projection (α : ℝ) (f : circleH4Domain T) :
    circleFixedProjectionH4 T (circleCenterDilation T α f) =
      (α:ℂ) • circleFixedProjectionH4 T f := by
  simp only [circleFixedProjectionH4,circleCenterDilation,Submodule.coe_add,
    Submodule.coe_sub,Submodule.coe_smul_of_tower,inner_add_right,inner_sub_right,
    inner_smul_right,circle_householder_anchor_h4_coe,circle_householder_anchor_unit,
    mul_one,sub_self,add_zero]
  module

theorem circle_center_dilation_remainder (α : ℝ) (f : circleH4Domain T) :
    circleCenterDilation T α f-circleFixedProjectionH4 T (circleCenterDilation T α f) =
      f-circleFixedProjectionH4 T f := by
  rw [circle_center_dilation_projection,circleCenterDilation]
  abel

set_option maxHeartbeats 1000000 in
theorem circle_reduced_center_congruence (A : Fin 5 → circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (h0c : A 0 (circleHouseholderAnchorH4 T) = 0)
    (h0r : ∀ f, inner ℂ (circleHouseholderAnchor T) (A 0 f) = 0)
    (h1 : inner ℂ (circleHouseholderAnchor T) (A 1 (circleHouseholderAnchorH4 T)) = 0)
    (h3 : inner ℂ (circleHouseholderAnchor T) (A 3 (circleHouseholderAnchorH4 T)) = 0)
    (h4 : ∀ f, A 4 f = ((-4*(2*Real.pi/T)^4:ℝ):ℂ) • (f:CircleL2 T))
    (α : ℝ) (f : circleH4Domain T) :
    circleDomainSymmetricPairing T
      (A 0+(α:ℂ) • A 1+(α:ℂ)^2 • A 2+(α:ℂ)^3 • A 3+(α:ℂ)^4 • A 4) f f =
    circleReducedBlochForm T (fun j => circleDomainSymmetricPairing T (A j)) α
      (circleCenterDilation T α f) (circleCenterDilation T α f) := by
  let B (j : Fin 5) := circleDomainSymmetricPairing T (A j)
  let a := circleHouseholderAnchorH4 T
  let u := circleFixedProjectionH4 T f
  let v := f-u
  let s := inner ℂ (circleHouseholderAnchor T) (f:CircleL2 T)
  let c : ℂ := ((-4*(2*Real.pi/T)^4:ℝ):ℂ)
  have hBl (j : Fin 5) (z : ℂ) (w x : circleH4Domain T) : B j (z • w) x = conj z*B j w x :=
    circle_domain_symmetric_smul_left T (A j) z w x
  have hBr (j : Fin 5) (z : ℂ) (w x : circleH4Domain T) : B j w (z • x) = z*B j w x :=
    circle_domain_symmetric_smul_right T (A j) z w x
  have hu : u = s • a := rfl
  have hav : inner ℂ (circleHouseholderAnchor T) (v:CircleL2 T) = 0 := by
    change inner ℂ (circleHouseholderAnchor T)
      ((f:CircleL2 T)-s • circleHouseholderAnchor T) = 0
    rw [inner_sub_right,inner_smul_right,circle_householder_anchor_unit,mul_one]
    exact sub_self s
  have huv : inner ℂ (u:CircleL2 T) (v:CircleL2 T) = 0 := by
    rw [hu]
    change inner ℂ (s • circleHouseholderAnchor T) (v:CircleL2 T) = 0
    rw [inner_smul_left,hav,mul_zero]
  have hvu := inner_eq_zero_symm.mpr huv
  have hz0a (w : circleH4Domain T) : B 0 a w = 0 := by
    change (1/2:ℂ)*(inner ℂ (circleHouseholderAnchor T) (A 0 w)+inner ℂ (A 0 a) (w:CircleL2 T)) = 0
    rw [h0r,h0c,inner_zero_left,zero_add,mul_zero]
  have hz0b (w : circleH4Domain T) : B 0 w a = 0 := by
    have hr := inner_eq_zero_symm.mpr (h0r w)
    change (1/2:ℂ)*(inner ℂ (w:CircleL2 T) (A 0 a)+inner ℂ (A 0 w) (circleHouseholderAnchor T)) = 0
    rw [h0c,inner_zero_right,hr,zero_add,mul_zero]
  have hz0u (w : circleH4Domain T) : B 0 u w = 0 := by
    rw [hu,hBl,hz0a,mul_zero]
  have hz0v (w : circleH4Domain T) : B 0 w u = 0 := by
    rw [hu,hBr,hz0b,mul_zero]
  have hodd (j : Fin 5) (hj : inner ℂ (circleHouseholderAnchor T) (A j a) = 0) : B j u u = 0 := by
    have hjrev := inner_eq_zero_symm.mpr hj
    have haa : B j a a = 0 := by
      change (1/2:ℂ)*(inner ℂ (circleHouseholderAnchor T) (A j a)+
        inner ℂ (A j a) (circleHouseholderAnchor T)) = 0
      rw [hj,hjrev,zero_add,mul_zero]
    rw [hu,hBl,hBr,haa,mul_zero,mul_zero]
  have htop (w z : circleH4Domain T) : B 4 w z = c*inner ℂ (w:CircleL2 T) (z:CircleL2 T) := by
    change (1/2:ℂ)*(inner ℂ (w:CircleL2 T) (A 4 z)+inner ℂ (A 4 w) (z:CircleL2 T)) = _
    rw [h4,h4,inner_smul_right,inner_smul_left,Complex.conj_ofReal]
    dsimp only [c]
    ring
  have hsplit (j : Fin 5) : B j f f = B j u u+B j u v+B j v u+B j v v := by
    conv_lhs => rw [show f = u+v by dsimp only [v]; abel]
    simp only [B,circle_domain_symmetric_add_left,circle_domain_symmetric_add_right]
    ring
  have hpoly : circleDomainSymmetricPairing T
      (A 0+(α:ℂ) • A 1+(α:ℂ)^2 • A 2+(α:ℂ)^3 • A 3+(α:ℂ)^4 • A 4) f f =
      B 0 f f+(α:ℂ)*B 1 f f+(α:ℂ)^2*B 2 f f+(α:ℂ)^3*B 3 f f+(α:ℂ)^4*B 4 f f := by
    simp only [B,circleDomainSymmetricPairing,LinearMap.add_apply,LinearMap.smul_apply,
      inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,map_pow,Complex.conj_ofReal]
    ring
  rw [hpoly,hsplit 0,hsplit 1,hsplit 2,hsplit 3,hsplit 4]
  simp only [circleReducedBlochForm]
  simp only [circle_center_dilation_remainder]
  simp only [circle_center_dilation_projection]
  change _ = B 2 ((α:ℂ) • u) ((α:ℂ) • u)+c*(α:ℂ)^2*
      inner ℂ (((α:ℂ) • u:circleH4Domain T):CircleL2 T) (((α:ℂ) • u:circleH4Domain T):CircleL2 T)+
    (B 1 ((α:ℂ) • u) v+B 1 v ((α:ℂ) • u))+
    (α:ℂ)*(B 2 ((α:ℂ) • u) v+B 2 v ((α:ℂ) • u))+
    (α:ℂ)^2*(B 3 ((α:ℂ) • u) v+B 3 v ((α:ℂ) • u))+
    B 0 v v+(α:ℂ)*B 1 v v+(α:ℂ)^2*B 2 v v+(α:ℂ)^3*B 3 v v+
    c*(α:ℂ)^4*inner ℂ (v:CircleL2 T) (v:CircleL2 T)
  rw [hz0u u,hz0u v,hz0v v,hodd 1 h1,hodd 3 h3,htop u u,htop u v,htop v u,htop v v,huv,hvu]
  simp only [hBl,hBr,
    Submodule.coe_smul_of_tower,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  ring

end Lemniscate
