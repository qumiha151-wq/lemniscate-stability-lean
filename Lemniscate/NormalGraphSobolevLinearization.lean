import Lemniscate.NormalGraphSobolevFlow
import Lemniscate.NormalGraphCoefficientDerivative
import Lemniscate.PeriodicSobolevOperator
import Lemniscate.PeriodicProfileEnergy
import Mathlib.Tactic.Module

/-! The genuine Frechet derivative of the H4-to-L2 normal-graph map.
The highest-order term uses the joint coefficient-times-L2 bilinear map.
Its coefficient derivative disappears at zero because the fourth derivative
of the zero height is zero. The lower term uses its proved Frechet derivative.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

def circleNormalGraphDerivative (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T :=
  (-4:ℂ) • circleSobolevCoordinate T 4 4+
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).comp
      ((normalGraphLowerOrderDerivative T K c).comp (circleNormalGraphCoordinates T))

theorem circle_normal_graph_hasFDerivAt
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) :
    HasFDerivAt (circleNormalGraphFlow T K c) (circleNormalGraphDerivative T K c) 0 := by
  let E := circleNormalGraphCoordinates T
  let A : CircleSobolevSpace T 4 → C(AddCircle T, ℂ) :=
    fun f => normalGraphPrincipalCoefficient T K (E f)
  let V : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T :=
    (4:ℂ) • circleSobolevCoordinate T 4 4
  obtain ⟨_,hzero,hcoeff⟩ := normal_graph_coefficients_smooth T K c
  have hAcont : ContDiffAt ℂ (⊤ : WithTop ℕ∞) A 0 := by
    have haE : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
        (normalGraphPrincipalCoefficient T K) (E (0 : CircleSobolevSpace T 4)) := by
      simpa only [map_zero] using (hcoeff 0 hzero).fst
    exact haE.comp 0 E.contDiff.contDiffAt
  let DA := fderiv ℂ A 0
  have hA : HasFDerivAt A DA 0 :=
    (hAcont.differentiableAt (by simp)).hasFDerivAt
  have hA0 : A 0 = -1 := by
    simp [A,E,normalGraphPrincipalCoefficient,graphMetricSquared,graphA]
  have hprod := (circleCoefficientMultiplyL2 T).hasFDerivAt_of_bilinear hA V.hasFDerivAt
  have hprod' : HasFDerivAt
      (fun f : CircleSobolevSpace T 4 => circleCoefficientMultiplyL2 T (A f) (V f))
      ((-4:ℂ) • circleSobolevCoordinate T 4 4) 0 := by
    apply hprod.congr_fderiv
    apply ContinuousLinearMap.ext
    intro f
    change circleCoefficientMultiplyL2 T (A 0) (V f)+
      circleCoefficientMultiplyL2 T (DA f) (V 0) =
        (-4:ℂ) • circleSobolevCoordinate T 4 4 f
    rw [hA0]
    simp only [map_zero,map_neg,ContinuousLinearMap.neg_apply,
      circle_coefficient_multiply_l2_apply,circle_multiply_l2_one,add_zero,V,
      smul_apply]
    module
  have hlower : HasFDerivAt (normalGraphLowerOrderCoefficient T K c)
      (normalGraphLowerOrderDerivative T K c) (E 0) := by
    simpa only [map_zero] using normal_graph_lower_order_hasFDerivAt T K c
  have hb := (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).hasFDerivAt.comp
    (0 : CircleSobolevSpace T 4) (hlower.comp 0 E.hasFDerivAt)
  exact hprod'.add hb

end Lemniscate
