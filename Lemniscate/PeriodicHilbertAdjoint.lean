import Lemniscate.PeriodicH4Density
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Connect the periodic H4 differential operator to Mathlib's genuine Hilbert
adjoint for densely defined unbounded operators. The formal expression is a
restriction of that adjoint; the reverse domain inclusion is not assumed. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleH4PMap (h h₁ h₂ : C(AddCircle T, ℂ)) :
    CircleL2 T →ₗ.[ℂ] CircleL2 T where
  domain := circleH4Domain T
  toFun := circleH4Operator T h h₁ h₂

noncomputable def circleH4FormalAdjointPMap (h h₁ : C(AddCircle T, ℂ)) :
    CircleL2 T →ₗ.[ℂ] CircleL2 T where
  domain := circleH4Domain T
  toFun := circleH4FormalAdjoint T h h₁

theorem circle_h4_pmap_dense (h h₁ h₂ : C(AddCircle T, ℂ)) :
    Dense ((circleH4PMap T h h₁ h₂).domain : Set (CircleL2 T)) := circle_h4_domain_dense T

theorem circle_h4_pmap_formal_adjoint (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    (circleH4PMap T h h₁ h₂).IsFormalAdjoint (circleH4FormalAdjointPMap T h h₁) := by
  intro f g
  exact circle_h4_formal_adjoint_green T h h₁ h₂ hh hh₁ hreal h₁real h₂real f g

theorem circle_h4_formal_le_hilbert_adjoint (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    circleH4FormalAdjointPMap T h h₁ ≤ (circleH4PMap T h h₁ h₂).adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint (circle_h4_pmap_dense T h h₁ h₂)
    (circle_h4_pmap_formal_adjoint T h h₁ h₂ hh hh₁ hreal h₁real h₂real)

theorem circle_h4_hilbert_adjoint_value (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (g : circleH4Domain T)
    (hg : (g : CircleL2 T) ∈ (circleH4PMap T h h₁ h₂).adjoint.domain) :
    (circleH4PMap T h h₁ h₂).adjoint ⟨g, hg⟩ = circleH4FormalAdjoint T h h₁ g := by
  apply LinearPMap.adjoint_apply_eq (circle_h4_pmap_dense T h h₁ h₂)
  intro f
  exact (circle_h4_pmap_formal_adjoint T h h₁ h₂ hh hh₁ hreal h₁real h₂real).symm g f

theorem circle_h4_hilbert_adjoint_closed (h h₁ h₂ : C(AddCircle T, ℂ)) :
    (circleH4PMap T h h₁ h₂).adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed (circle_h4_pmap_dense T h h₁ h₂)

theorem circle_h4_hilbert_adjoint_dense (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    Dense ((circleH4PMap T h h₁ h₂).adjoint.domain : Set (CircleL2 T)) :=
  (circle_h4_domain_dense T).mono
    (circle_h4_formal_le_hilbert_adjoint T h h₁ h₂ hh hh₁ hreal h₁real h₂real).1

theorem circle_h4_pmap_closable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) : (circleH4PMap T h h₁ h₂).IsClosable := by
  have hd : Dense ((circleH4FormalAdjointPMap T h h₁).domain : Set (CircleL2 T)) :=
    circle_h4_domain_dense T
  have hl : circleH4PMap T h h₁ h₂ ≤ (circleH4FormalAdjointPMap T h h₁).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd
      (circle_h4_pmap_formal_adjoint T h h₁ h₂ hh hh₁ hreal h₁real h₂real).symm
  exact (LinearPMap.adjoint_isClosed (T := circleH4FormalAdjointPMap T h h₁) hd).isClosable.leIsClosable hl

end Lemniscate
