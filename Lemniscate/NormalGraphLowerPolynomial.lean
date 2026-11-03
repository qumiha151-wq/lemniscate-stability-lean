import Lemniscate.NormalGraphPolynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.VecNotation

/-! The lower-order rational flow is cubic in h_ss and affine in h_sss,
with only one mixed monomial h_ss*h_sss. Its coefficients are recovered by
six finite evaluations of the same rational flow. No unit hypothesis is
needed: the scalar inverse factors are constant in these two variables.
-/
noncomputable section
namespace Lemniscate
open Complex

/-- Coefficients in the order B0, B1, B2, B3, C0, C1, corresponding to
1, v, v^2, v^3, w, v*w. The defining samples use the existing flow itself. -/
def normalGraphLowerCoefficients {R : Type*} [CommRing R] [Algebra ℝ R]
    (K : BackgroundJetOver R) (c : ℝ) (u₀ u₁ : R) : Fin 6 → R :=
  let b : R → R → R := fun v w => normalGraphRationalFlow K c ⟨u₀,u₁,v,w,0⟩
  let B₀ := b 0 0
  let d₁ := b 1 0-B₀
  let dm := b (-1) 0-B₀
  let d₂ := b 2 0-B₀
  let B₂ := (1/2:ℝ) • (d₁+dm)
  let B₃ := (1/6:ℝ) • (d₂-2*d₁-2*B₂)
  let B₁ := d₁-B₂-B₃
  let C₀ := b 0 1-B₀
  let C₁ := b 1 1-b 1 0-C₀
  ![B₀,B₁,B₂,B₃,C₀,C₁]

set_option maxHeartbeats 2000000 in
theorem normal_graph_lower_polynomial (K : BackgroundJetOver ℂ) (c : ℝ)
    (u₀ u₁ v w : ℂ) :
    let B := normalGraphLowerCoefficients K c u₀ u₁
    normalGraphRationalFlow K c ⟨u₀,u₁,v,w,0⟩ =
      B 0+B 1*v+B 2*v^2+B 3*v^3+B 4*w+B 5*v*w := by
  have hA (v w : ℂ) : graphA K ⟨u₀,u₁,v,w,0⟩ =
      graphA K ⟨u₀,u₁,0,0,0⟩ := rfl
  have hAs (v w : ℂ) : graphAs K ⟨u₀,u₁,v,w,0⟩ =
      graphAs K ⟨u₀,u₁,0,0,0⟩ := rfl
  have hH (v w : ℂ) : graphMetricSquared K ⟨u₀,u₁,v,w,0⟩ =
      graphMetricSquared K ⟨u₀,u₁,0,0,0⟩ := rfl
  dsimp only [normalGraphLowerCoefficients]
  simp only [Matrix.cons_val_zero,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  simp only [normalGraphRationalFlow,graphCurvatureNumeratorSS,
    graphCurvatureNumeratorS,graphCurvatureNumerator,graphMetricSquaredS,
    graphMetricSquaredSS,graphSupportNumerator,graphAss,hA,hAs,hH,
    Ring.inverse_eq_inv,real_smul]
  push_cast
  ring

end Lemniscate
