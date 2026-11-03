import Lemniscate.PeriodicSobolevProducts
import Lemniscate.PeriodicCoefficientAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-! Two-point estimates for the second-derivative nonlinearities. All bounds
come from the mixed Sobolev product theorem and exact multilinear differences.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

/-- Quadratic and cubic derivative terms have the mixed H2-H4 difference
bounds needed for a contraction estimate. -/
theorem circle_sobolev_product_difference_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ f g : CircleSobolevSpace T 4,
      let H₂ : CircleSobolevSpace T 4 → ℝ :=
        fun u => ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 u)‖
      let d := f-g
      let R := (H₂ f+H₂ g)*‖d‖+(‖f‖+‖g‖)*H₂ d
      ‖circleMultiplyL2 T (circleSobolevContinuousJet T f 2)
          (circleSobolevCoordinate T 4 2 f)-
        circleMultiplyL2 T (circleSobolevContinuousJet T g 2)
          (circleSobolevCoordinate T 4 2 g)‖ ≤ K*R ∧
      ‖circleMultiplyL2 T ((circleSobolevContinuousJet T f 2)^2)
          (circleSobolevCoordinate T 4 2 f)-
        circleMultiplyL2 T ((circleSobolevContinuousJet T g 2)^2)
          (circleSobolevCoordinate T 4 2 g)‖ ≤ K*(H₂ f+H₂ g)*R ∧
      ‖circleMultiplyL2 T (circleSobolevContinuousJet T f 2)
          (circleSobolevCoordinate T 4 3 f)-
        circleMultiplyL2 T (circleSobolevContinuousJet T g 2)
          (circleSobolevCoordinate T 4 3 g)‖ ≤ K*R := by
  obtain ⟨C,hC,hbound⟩ := circle_sobolev_second_product_bounds T
  refine ⟨2*C,by positivity,fun f g => ?_⟩
  let H₂ : CircleSobolevSpace T 4 → ℝ :=
    fun u => ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 u)‖
  let J : CircleSobolevSpace T 4 →L[ℂ] C(AddCircle T, ℂ) :=
    (ContinuousLinearMap.proj (2 : Fin 4)).comp (circleSobolevContinuousJet T)
  let P := circleSobolevCoordinate T 4 2
  let Q := circleSobolevCoordinate T 4 3
  let M := circleCoefficientMultiplyL2 T
  let d := f-g
  let R := (H₂ f+H₂ g)*‖d‖+(‖f‖+‖g‖)*H₂ d
  have hH₂ (u : CircleSobolevSpace T 4) : 0 ≤ H₂ u := norm_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hB (u v : CircleSobolevSpace T 4) :
      ‖M (J u) (P v)‖ ≤ C*‖u‖*H₂ v := (hbound u v 0).1
  have hCub (u v w : CircleSobolevSpace T 4) :
      ‖M (J u*J v) (P w)‖ ≤ C*(H₂ u*‖v‖+H₂ v*‖u‖)*H₂ w :=
    (hbound u v w).2.1
  have hD (u v : CircleSobolevSpace T 4) :
      ‖M (J u) (Q v)‖ ≤ C*(H₂ u*‖v‖+H₂ v*‖u‖) := (hbound u v 0).2.2
  have hsplitB : M (J f) (P f)-M (J g) (P g) =
      M (J d) (P f)+M (J g) (P d) := by
    dsimp only [d]
    simp only [map_sub,sub_apply]
    abel
  have hsplitC : M ((J f)^2) (P f)-M ((J g)^2) (P g) =
      M (J d*J f) (P f)+M (J g*J d) (P f)+M (J g*J g) (P d) := by
    dsimp only [d]
    simp only [pow_two,map_sub,sub_mul,mul_sub,sub_apply]
    abel
  have hsplitD : M (J f) (Q f)-M (J g) (Q g) =
      M (J d) (Q f)+M (J g) (Q d) := by
    dsimp only [d]
    simp only [map_sub,sub_apply]
    abel
  have hBraw : ‖M (J f) (P f)-M (J g) (P g)‖ ≤ C*R := by
    calc
      ‖M (J f) (P f)-M (J g) (P g)‖ =
          ‖M (J d) (P f)+M (J g) (P d)‖ := congrArg norm hsplitB
      _ ≤ ‖M (J d) (P f)‖+‖M (J g) (P d)‖ := norm_add_le _ _
      _ ≤ C*‖d‖*H₂ f+C*‖g‖*H₂ d := add_le_add (hB d f) (hB g d)
      _ ≤ C*R := by
        have hrem : 0 ≤ C*(H₂ g*‖d‖+‖f‖*H₂ d) := by positivity
        dsimp only [R]
        linear_combination hrem
  have hCraw : ‖M ((J f)^2) (P f)-M ((J g)^2) (P g)‖ ≤
      (2*C)*(H₂ f+H₂ g)*R := by
    calc
      ‖M ((J f)^2) (P f)-M ((J g)^2) (P g)‖ =
          ‖M (J d*J f) (P f)+M (J g*J d) (P f)+M (J g*J g) (P d)‖ :=
        congrArg norm hsplitC
      _ ≤ (‖M (J d*J f) (P f)‖+‖M (J g*J d) (P f)‖)+
          ‖M (J g*J g) (P d)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (C*(H₂ d*‖f‖+H₂ f*‖d‖)*H₂ f+
          C*(H₂ g*‖d‖+H₂ d*‖g‖)*H₂ f)+
          C*(H₂ g*‖g‖+H₂ g*‖g‖)*H₂ d :=
        add_le_add (add_le_add (hCub d f f) (hCub g d f)) (hCub g g d)
      _ ≤ (2*C)*(H₂ f+H₂ g)*R := by
        have hrem : 0 ≤
            C*((H₂ f)^2+3*H₂ f*H₂ g+2*(H₂ g)^2)*‖d‖+
              C*(H₂ f*‖f‖+H₂ f*‖g‖+2*H₂ g*‖f‖)*H₂ d := by positivity
        dsimp only [R]
        linear_combination hrem
  have hDraw : ‖M (J f) (Q f)-M (J g) (Q g)‖ ≤ C*R := by
    calc
      ‖M (J f) (Q f)-M (J g) (Q g)‖ =
          ‖M (J d) (Q f)+M (J g) (Q d)‖ := congrArg norm hsplitD
      _ ≤ ‖M (J d) (Q f)‖+‖M (J g) (Q d)‖ := norm_add_le _ _
      _ ≤ C*(H₂ d*‖f‖+H₂ f*‖d‖)+C*(H₂ g*‖d‖+H₂ d*‖g‖) :=
        add_le_add (hD d f) (hD g d)
      _ = C*R := by dsimp only [R]; ring
  have hdouble : C*R ≤ (2*C)*R := by nlinarith [mul_nonneg hC.le hR]
  change ‖M (J f) (P f)-M (J g) (P g)‖ ≤ (2*C)*R ∧
    ‖M ((J f)^2) (P f)-M ((J g)^2) (P g)‖ ≤ (2*C)*(H₂ f+H₂ g)*R ∧
    ‖M (J f) (Q f)-M (J g) (Q g)‖ ≤ (2*C)*R
  exact ⟨hBraw.trans hdouble,hCraw,hDraw.trans hdouble⟩

end Lemniscate
