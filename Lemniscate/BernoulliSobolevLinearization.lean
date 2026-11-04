import Lemniscate.NormalGraphSobolevLinearization
import Lemniscate.PeriodicSobolevOperator
import Mathlib.Tactic.LinearCombination

/-! The Bernoulli profile is an equilibrium of the normal-graph equation.
Its genuine Frechet derivative from H4 to L2 agrees with the previously
identified periodic differential operator. The background jet uses physical
arclength; the Sobolev coordinates already include the factors from ds = dx/sqrt 2.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

def circleBernoulliBackground (q p : C(AddCircle T, ℂ)) :
    BackgroundJetOver C(AddCircle T, ℂ) where
  k := (3:ℂ) • q
  ks := ((3*Real.sqrt 2:ℝ):ℂ) • p
  kss := (-6:ℂ) • (q^3)
  ksss := ((-18*Real.sqrt 2:ℝ):ℂ) • (q^2*p)
  eta := -(q^3)
  b := ((Real.sqrt 2:ℝ):ℂ) • (q*p)

private theorem bernoulli_lower_order_zero (q p : C(AddCircle T, ℂ)) :
    normalGraphLowerOrderCoefficient T (circleBernoulliBackground T q p) (15/2) 0 = 0 := by
  ext x
  simp [normalGraphLowerOrderCoefficient,normalGraphLowerOrderCoefficientOver,normalGraphRationalFlow,
    graphCurvatureNumeratorSS,graphCurvatureNumeratorS,graphCurvatureNumerator,
    graphMetricSquaredSS,graphMetricSquaredS,graphMetricSquared,
    graphSupportNumerator,graphAss,graphAs,graphA,circleBernoulliBackground,
    real_smul,smul_eq_mul]
  <;> ring

private theorem bernoulli_lower_order_derivative
    (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) (f : CircleSobolevSpace T 4) :
    normalGraphLowerOrderDerivative T (circleBernoulliBackground T q p) (15/2)
        (circleNormalGraphCoordinates T f) =
      (-45:ℂ) • ((q^2)*circleSobolevContinuousJet T f 2)-
      (75:ℂ) • ((q*p)*circleSobolevContinuousJet T f 1)-
      (69/2:ℂ) • circleSobolevContinuousJet T f 0-
      (45/2:ℂ) • ((q^4)*circleSobolevContinuousJet T f 0) := by
  have hs : ((Real.sqrt 2:ℝ):ℂ)^2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))
  rw [circle_normal_graph_coordinates]
  ext x
  simp only [normalGraphLowerOrderDerivative,circleBernoulliBackground,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.mul_apply',ContinuousMap.smul_apply,
    ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.mul_apply,
    ContinuousMap.pow_apply,ContinuousMap.natCast_apply,ContinuousMap.one_apply,
    real_smul,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply]
  push_cast
  linear_combination
    -((75/2:ℂ)*(q x)*(p x)*(circleSobolevContinuousJet T f 1 x)+
      27*(p x)^2*(circleSobolevContinuousJet T f 0 x))*hs-
    (27*(circleSobolevContinuousJet T f 0 x))*(he x)

/-- The rescaled elastic normal-graph flow has the Bernoulli profile as an
equilibrium, and its H4-to-L2 Frechet derivative is the periodic operator.
The first integral is used only to combine the zeroth-order coefficient. -/
theorem bernoulli_sobolev_flow_linearization
    (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) :
    circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) 0 = 0 ∧
      HasFDerivAt
        (circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2))
        (circleSobolevOperator T (q^2) ((2:ℂ) • (q*p))
          (1-(3:ℂ) • (q^4))) 0 := by
  have hzero := bernoulli_lower_order_zero T q p
  have hoperator :
      circleNormalGraphDerivative T (circleBernoulliBackground T q p) (15/2) =
        circleSobolevOperator T (q^2) ((2:ℂ) • (q*p))
          (1-(3:ℂ) • (q^4)) := by
    apply ContinuousLinearMap.ext
    intro f
    have hmul (a : C(AddCircle T, ℂ)) (j : Fin 4) :
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
            (a*circleSobolevContinuousJet T f j) =
          circleMultiplyL2 T a (circleSobolevCoordinate T 4 j.castSucc f) := by
      change circleContinuousL2 T (a*circleSobolevContinuousJet T f j) = _
      rw [← circle_multiply_l2_continuous,circle_sobolev_continuous_jet_l2]
    have hbase :
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
            (circleSobolevContinuousJet T f 0) = circleSobolevCoordinate T 4 0 f := by
      exact circle_sobolev_continuous_jet_l2 T f 0
    rw [circle_sobolev_operator_profile]
    simp only [circleNormalGraphDerivative,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply]
    rw [bernoulli_lower_order_derivative T q p he f]
    simp [hmul,hbase] <;> module
  refine ⟨?_,?_⟩
  · simp [circleNormalGraphFlow,hzero,circleContinuousL2]
  · rw [← hoperator]
    exact circle_normal_graph_hasFDerivAt T (circleBernoulliBackground T q p) (15/2)

end Lemniscate
