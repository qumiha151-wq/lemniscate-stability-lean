import Lemniscate.PeriodicSobolevDerivatives

/-! The actual continuous derivatives of orders zero through three of H4 data.
The fourth derivative remains an L2 coordinate. The map into the existing
unbounded H4 domain retains that domain's inherited L2 norm. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

private def circleSobolevH4ToH1 (j : Fin 4) :
    CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 1 :=
  ![(circleSobolevInclusion T 1).comp
      ((circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)),
    (circleSobolevInclusion T 1).comp
      ((circleSobolevInclusion T 2).comp (circleSobolevDerivative T 3)),
    (circleSobolevInclusion T 1).comp
      ((circleSobolevDerivative T 2).comp (circleSobolevDerivative T 3)),
    (circleSobolevDerivative T 1).comp
      ((circleSobolevDerivative T 2).comp (circleSobolevDerivative T 3))] j

/-- The continuous representatives of derivatives of orders 0,1,2,3. -/
def circleSobolevContinuousJet :
    CircleSobolevSpace T 4 →L[ℂ] (Fin 4 → C(AddCircle T, ℂ)) :=
  ContinuousLinearMap.pi fun j =>
    (circleSobolevH1Embedding T).comp (circleSobolevH4ToH1 T j)

theorem circle_sobolev_continuous_jet_l2 (f : CircleSobolevSpace T 4) (j : Fin 4) :
    circleContinuousL2 T (circleSobolevContinuousJet T f j) =
      circleSobolevCoordinate T 4 j.castSucc f := by
  change circleContinuousL2 T
      (circleSobolevH1Embedding T (circleSobolevH4ToH1 T j f)) = _
  rw [circle_sobolev_h1_embedding_l2]
  fin_cases j <;> rfl

theorem circle_sobolev_continuous_jet_deriv (f : CircleSobolevSpace T 4) (j : Fin 3) :
    HasCircleDeriv T (circleSobolevContinuousJet T f j.castSucc)
      (circleSobolevContinuousJet T f j.succ) := by
  apply circle_classical_deriv_of_continuous_weak T
  rw [circle_sobolev_continuous_jet_l2,circle_sobolev_continuous_jet_l2]
  simpa only [circle_sobolev_coordinate_apply,Fin.castSucc_succ] using
    circle_sobolev_weak_deriv T 4 f j.castSucc

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
