import Lemniscate.NormalGraphPolynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-! The complex scalar first variation of the rational normal-graph flow.
This is a genuine complex HasDerivAt statement. Identifying a Banach-space
Fréchet derivative requires the separately proved smooth coefficient map. -/
noncomputable section
namespace Lemniscate
open Complex

private theorem complex_quadratic_hasDerivAt (a d R : ℂ) :
    HasDerivAt (fun ε : ℂ => a+ε*d+ε^2*R) d 0 := by
  have hd := ((hasDerivAt_const (0:ℂ) a).add
    ((hasDerivAt_id (0:ℂ)).mul_const d)).add
      (((hasDerivAt_id (0:ℂ)).pow 2).mul_const R)
  convert! hd using 1 <;> norm_num

theorem normal_graph_complex_rational_flow_hasDerivAt
    (K : BackgroundJetOver ℂ) (c : ℝ) (F : HeightJetOver ℂ) :
    HasDerivAt (fun ε : ℂ => normalGraphRationalFlow K c
      ⟨ε*F.h,ε*F.hs,ε*F.hss,ε*F.hsss,ε*F.hssss⟩)
      (-F.hssss-(5/2:ℂ)*K.k^2*F.hss-(5*K.k*K.ks-(c:ℂ)*K.b)*F.hs-
        (3*K.ks^2+4*K.k*K.kss+(3/2:ℂ)*K.k^4+(c:ℂ))*F.h) 0 := by
  have hA : HasDerivAt (fun ε : ℂ => graphA K (normalGraphScaleHeight ε F))
      (-K.k*F.h) 0 := by
    convert! complex_quadratic_hasDerivAt 1 (-K.k*F.h) 0 using 1
    funext ε
    dsimp only [graphA,normalGraphScaleHeight]
    ring
  have hH : HasDerivAt (fun ε : ℂ => graphMetricSquared K (normalGraphScaleHeight ε F))
      (-2*K.k*F.h) 0 := by
    convert! complex_quadratic_hasDerivAt 1 (-2*K.k*F.h)
      (K.k^2*F.h^2+F.hs^2) using 1
    funext ε
    dsimp only [graphMetricSquared,graphA,normalGraphScaleHeight]
    ring
  have hH₁ : HasDerivAt (fun ε : ℂ => graphMetricSquaredS K (normalGraphScaleHeight ε F))
      (-2*(K.ks*F.h+K.k*F.hs)) 0 := by
    convert! complex_quadratic_hasDerivAt 0 (-2*(K.ks*F.h+K.k*F.hs))
      (2*K.k*F.h*(K.ks*F.h+K.k*F.hs)+2*F.hs*F.hss) using 1
    funext ε
    dsimp only [graphMetricSquaredS,graphA,graphAs,normalGraphScaleHeight]
    ring
  have hH₂ : HasDerivAt (fun ε : ℂ => graphMetricSquaredSS K (normalGraphScaleHeight ε F))
      (-2*(K.kss*F.h+2*K.ks*F.hs+K.k*F.hss)) 0 := by
    convert! complex_quadratic_hasDerivAt 0 (-2*(K.kss*F.h+2*K.ks*F.hs+K.k*F.hss))
      (2*(K.ks*F.h+K.k*F.hs)^2+
        2*K.k*F.h*(K.kss*F.h+2*K.ks*F.hs+K.k*F.hss)+2*F.hss^2+2*F.hs*F.hsss) using 1
    funext ε
    dsimp only [graphMetricSquaredSS,graphA,graphAs,graphAss,normalGraphScaleHeight]
    ring
  have hN : HasDerivAt (fun ε : ℂ => graphCurvatureNumerator K (normalGraphScaleHeight ε F))
      (F.hss-2*K.k^2*F.h) 0 := by
    convert! complex_quadratic_hasDerivAt K.k (F.hss-2*K.k^2*F.h)
      (K.k^3*F.h^2-K.k*F.h*F.hss+K.ks*F.h*F.hs+2*K.k*F.hs^2) using 1
    funext ε
    dsimp only [graphCurvatureNumerator,graphA,normalGraphScaleHeight]
    ring
  have hN₁ : HasDerivAt (fun ε : ℂ => graphCurvatureNumeratorS K (normalGraphScaleHeight ε F))
      (F.hsss-4*K.k*K.ks*F.h-2*K.k^2*F.hs) 0 := by
    convert! complex_quadratic_hasDerivAt K.ks (F.hsss-4*K.k*K.ks*F.h-2*K.k^2*F.hs)
      (3*K.k^2*K.ks*F.h^2+2*K.k^3*F.h*F.hs-K.k*F.h*F.hsss+
        K.kss*F.h*F.hs+3*K.ks*F.hs^2+3*K.k*F.hs*F.hss) using 1
    funext ε
    dsimp only [graphCurvatureNumeratorS,graphA,graphAs,normalGraphScaleHeight]
    ring
  have hN₂ : HasDerivAt (fun ε : ℂ => graphCurvatureNumeratorSS K (normalGraphScaleHeight ε F))
      (F.hssss-4*(K.ks^2+K.k*K.kss)*F.h-8*K.k*K.ks*F.hs-2*K.k^2*F.hss) 0 := by
    convert! complex_quadratic_hasDerivAt K.kss
      (F.hssss-4*(K.ks^2+K.k*K.kss)*F.h-8*K.k*K.ks*F.hs-2*K.k^2*F.hss)
      ((6*K.k*K.ks^2+3*K.k^2*K.kss)*F.h^2+12*K.k^2*K.ks*F.h*F.hs+
        2*K.k^3*F.hs^2+2*K.k^3*F.h*F.hss-K.ks*F.h*F.hsss+
        2*K.k*F.hs*F.hsss-K.k*F.h*F.hssss+K.ksss*F.h*F.hs+
        4*K.kss*F.hs^2+K.kss*F.h*F.hss+9*K.ks*F.hs*F.hss+3*K.k*F.hss^2) using 1
    funext ε
    dsimp only [graphCurvatureNumeratorSS,graphA,graphAs,graphAss,normalGraphScaleHeight]
    ring
  have hP : HasDerivAt (fun ε : ℂ => graphSupportNumerator K (normalGraphScaleHeight ε F))
      (-K.k*F.h*K.eta+F.h-K.b*F.hs) 0 := by
    convert! complex_quadratic_hasDerivAt K.eta (-K.k*F.h*K.eta+F.h-K.b*F.hs)
      (-K.k*F.h^2) using 1
    funext ε
    dsimp only [graphSupportNumerator,graphA,normalGraphScaleHeight]
    ring
  have hiA : HasDerivAt (fun ε : ℂ => (graphA K (normalGraphScaleHeight ε F))⁻¹)
      (K.k*F.h) 0 := by
    convert! hA.inv (by simp [graphA,normalGraphScaleHeight]) using 1 <;>
      simp only [graphA,normalGraphScaleHeight,zero_mul,mul_zero,sub_zero,
        one_pow,div_one,neg_neg] <;> ring
  have hiH : HasDerivAt (fun ε : ℂ => (graphMetricSquared K (normalGraphScaleHeight ε F))⁻¹)
      (2*K.k*F.h) 0 := by
    convert! hH.inv (by simp [graphMetricSquared,graphA,normalGraphScaleHeight]) using 1 <;>
      simp only [graphMetricSquared,graphA,normalGraphScaleHeight,zero_mul,mul_zero,
        sub_zero,one_pow,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,div_one,neg_neg] <;> ring
  have hd₀ := hN₂.mul (hiH.pow 2)
  have hd₁ := ((hN₁.mul hH₁).mul (hiH.pow 3)).const_mul (7/2:ℂ)
  have hd₂ := ((hN.mul hH₂).mul (hiH.pow 3)).const_mul (3/2:ℂ)
  have hd₃ := ((hN.mul (hH₁.pow 2)).mul (hiH.pow 4)).const_mul (9/2:ℂ)
  have hd₄ := ((hN.pow 3).mul (hiH.pow 4)).const_mul (1/2:ℂ)
  have hd₅ := hP.const_mul (c:ℂ)
  have hdB := ((((hd₀.sub hd₁).sub hd₂).add hd₃).add hd₄).add hd₅
  have hd := (hiA.mul hdB).neg
  convert! hd using 1
  · funext ε
    simp only [normalGraphRationalFlow,normalGraphScaleHeight,Ring.inverse_eq_inv,real_smul,
      Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.pow_apply]
    push_cast
    ring
  · simp only [normalGraphScaleHeight,graphCurvatureNumeratorSS,graphCurvatureNumeratorS,
      graphCurvatureNumerator,graphMetricSquaredSS,graphMetricSquaredS,
      graphMetricSquared,graphSupportNumerator,graphAss,graphAs,graphA,
      Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.pow_apply,
      zero_mul,mul_zero,add_zero,zero_add,sub_zero,one_mul,mul_one,one_pow,
      zero_pow (by decide : (2:ℕ) ≠ 0),inv_one,Nat.reduceSub,Nat.cast_ofNat]
    ring

end Lemniscate
