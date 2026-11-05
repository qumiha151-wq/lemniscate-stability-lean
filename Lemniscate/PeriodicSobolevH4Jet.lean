import Lemniscate.PeriodicSobolevClassicalJet

/-! The actual continuous derivatives of orders zero through three of H4 data.
The fourth derivative remains an L2 coordinate. The map into the existing
unbounded H4 domain retains that domain's inherited L2 norm. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

/-- The H4 specialization of the general continuous classical jet. -/
abbrev circleSobolevContinuousJet :
    CircleSobolevSpace T 4 →L[ℂ] (Fin 4 → C(AddCircle T, ℂ)) :=
  circleSobolevClassicalJet T 3

/-- The value in the original weak H4 operator domain. Its source has the
complete Sobolev norm; its target has the original inherited L2 norm. -/
def circleSobolevToH4Domain : CircleSobolevSpace T 4 →L[ℂ] circleH4Domain T :=
  (circleSobolevCoordinate T 4 0).codRestrict (circleH4Domain T)
    (fun f => (circle_sobolev_four_range T _).mp ⟨f,rfl⟩)

@[simp] theorem circle_sobolev_to_h4_domain_coe (f : CircleSobolevSpace T 4) :
    ((circleSobolevToH4Domain T f) : CircleL2 T) = circleSobolevCoordinate T 4 0 f := rfl

theorem circle_sobolev_h4_jet (f : CircleSobolevSpace T 4) :
    circleH4Jet T (circleSobolevToH4Domain T f) =
      { first := circleSobolevCoordinate T 4 1 f
        second := circleSobolevCoordinate T 4 2 f
        third := circleSobolevCoordinate T 4 3 f
        fourth := circleSobolevCoordinate T 4 4 f
        hfirst := circle_sobolev_weak_deriv T 4 f 0
        hsecond := circle_sobolev_weak_deriv T 4 f 1
        hthird := circle_sobolev_weak_deriv T 4 f 2
        hfourth := circle_sobolev_weak_deriv T 4 f 3 } :=
  circle_h4_jet_unique T _ _ _

end Lemniscate
