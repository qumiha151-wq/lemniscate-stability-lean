import Lemniscate.ComplexRows
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! A finite quadratic-form certificate from a nonnegative factorization
and a bounded symmetric remainder. The factors need not be exact or invertible. -/
namespace Lemniscate
open Finset Matrix Complex
open scoped ComplexConjugate

private theorem real_factor_energy_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A L R : Matrix ι ι ℝ) (d δ : ι → ℝ) (g ε : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hR : ∀ i j, R i j = R j i)
    (hrow : ∀ i, ∑ j, |R i j| ≤ ε)
    (hA : ∀ i j, A i j = -(L * diagonal d * Lᵀ) i j -
      (if i = j then δ i+g else 0)+R i j) (x : ι → ℝ) :
    (∑ i, ∑ j, A i j*x i*x j) ≤ ∑ i, (ε-g-δ i)*(x i)^2 := by
  have hp : (L * diagonal d * Lᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same L
  have hk : 0 ≤ ∑ i, ∑ j, (L * diagonal d * Lᵀ) i j*x i*x j := by
    have h := hp.dotProduct_mulVec_nonneg x
    simpa only [dotProduct,mulVec,star_trivial,Finset.mul_sum,
      mul_comm,mul_left_comm,mul_assoc] using h
  have hr := weighted_double_sum_bound Finset.univ R (fun _ => 1) x
    (by intro i _; norm_num) (by intro i _ j _; exact hR i j)
  simp only [div_self one_ne_zero,mul_one] at hr
  have hr' : (∑ i, ∑ j, R i j*x i*x j) ≤ ∑ i, ε*(x i)^2 := by
    apply hr.trans
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  have heq : (∑ i, ∑ j, A i j*x i*x j) =
      -(∑ i, ∑ j, (L * diagonal d * Lᵀ) i j*x i*x j)-
        (∑ i, (δ i+g)*(x i)^2)+(∑ i, ∑ j, R i j*x i*x j) := by
    simp [hA,sub_mul,add_mul,neg_mul,ite_mul,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,Finset.sum_neg_distrib,pow_two,mul_assoc]
  have hb : (∑ i, (ε-g-δ i)*(x i)^2) =
      (∑ i, ε*(x i)^2)-(∑ i, (δ i+g)*(x i)^2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq,hb]
  linarith only [hk,hr']

theorem real_form_bound_complex {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (b : ι → ℝ)
    (h : ∀ x : ι → ℝ, (∑ i, ∑ j, A i j*x i*x j) ≤ ∑ i, b i*(x i)^2)
    (v : ι → ℂ) :
    (∑ i, ∑ j, conj (v i)*(A i j:ℂ)*v j).re ≤ ∑ i, b i*‖v i‖^2 := by
  have heq (i j : ι) : (conj (v i)*(A i j:ℂ)*v j).re =
      A i j*(v i).re*(v j).re+A i j*(v i).im*(v j).im := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_add]
    ring
  have hn (i : ι) : ‖v i‖^2 = (v i).re^2+(v i).im^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  have hr := add_le_add (h (fun i => (v i).re)) (h (fun i => (v i).im))
  change Complex.reCLM (∑ i, ∑ j, conj (v i)*(A i j:ℂ)*v j) ≤ _
  simp only [map_sum]
  change (∑ i, ∑ j, (conj (v i)*(A i j:ℂ)*v j).re) ≤ _
  simpa only [heq,hn,mul_add,Finset.sum_add_distrib] using hr

theorem finite_factor_energy_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A L R : Matrix ι ι ℝ) (d δ : ι → ℝ) (g ε : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hR : ∀ i j, R i j = R j i)
    (hrow : ∀ i, ∑ j, |R i j| ≤ ε)
    (hA : ∀ i j, A i j = -(L * diagonal d * Lᵀ) i j -
      (if i = j then δ i+g else 0)+R i j) (v : ι → ℂ) :
    (∑ i, ∑ j, conj (v i)*(A i j:ℂ)*v j).re ≤ ∑ i, (ε-g-δ i)*‖v i‖^2 :=
  real_form_bound_complex A _ (real_factor_energy_bound A L R d δ g ε hd hR hrow hA) v

/-- Absorb the interaction using a single squared Cauchy bound. -/
theorem finite_tail_energy_bound (a b c X Y D W : ℝ)
    (hD : 0 ≤ D) (hW : 0 ≤ W) (hXY : 2*Y ≤ W)
    (ha : a ≤ -X-D) (hc : c ≤ -W) (hb : b^2 ≤ D*W/2) :
    a+2*b+c ≤ -(X+Y) := by
  have hy : 2*b ≤ D+W/2 := two_mul_le_add_of_sq_le_mul hD
    (div_nonneg hW (by norm_num)) (by nlinarith only [hb])
  linarith only [ha,hc,hy,hXY]

theorem finite_weighted_coupling {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (B : ι → κ → ℂ) (δ : ι → ℝ) (ω : κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hδ : ∀ i ∈ I, 0 < δ i) (hω : ∀ j ∈ J, 0 < ω j) :
    ‖∑ i ∈ I, ∑ j ∈ J, conj (x i)*B i j*y j‖^2 ≤
      (∑ i ∈ I, ∑ j ∈ J, ‖B i j‖^2/(δ i*ω j))*
        (∑ i ∈ I, δ i*‖x i‖^2)*(∑ j ∈ J, ω j*‖y j‖^2) := by
  let f : ι × κ → ℝ := fun ij => ‖B ij.1 ij.2‖^2/(δ ij.1*ω ij.2)
  let g : ι × κ → ℝ := fun ij => (δ ij.1*‖x ij.1‖^2)*(ω ij.2*‖y ij.2‖^2)
  let r : ι × κ → ℝ := fun ij => ‖B ij.1 ij.2‖*‖x ij.1‖*‖y ij.2‖
  have hf (ij : ι × κ) (hij : ij ∈ I ×ˢ J) : 0 ≤ f ij := by
    have hd := hδ ij.1 (Finset.mem_product.mp hij).1
    have hw := hω ij.2 (Finset.mem_product.mp hij).2
    dsimp only [f]
    positivity
  have hg (ij : ι × κ) (hij : ij ∈ I ×ˢ J) : 0 ≤ g ij := by
    have hd := hδ ij.1 (Finset.mem_product.mp hij).1
    have hw := hω ij.2 (Finset.mem_product.mp hij).2
    dsimp only [g]
    positivity
  have ht (ij : ι × κ) (hij : ij ∈ I ×ˢ J) : (r ij)^2 ≤ f ij*g ij := by
    have hd := ne_of_gt (hδ ij.1 (Finset.mem_product.mp hij).1)
    have hw := ne_of_gt (hω ij.2 (Finset.mem_product.mp hij).2)
    dsimp only [r,f,g]
    apply le_of_eq
    field_simp
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (I ×ˢ J) hf hg ht
  have hn : ‖∑ i ∈ I, ∑ j ∈ J, conj (x i)*B i j*y j‖ ≤ ∑ ij ∈ I ×ˢ J, r ij := by
    rw [Finset.sum_product]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro j hj
    simp only [r,norm_mul,norm_conj]
    ring
  have h := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc
  have hgSum : (∑ ij ∈ I ×ˢ J, g ij) =
      (∑ i ∈ I, δ i*‖x i‖^2)*(∑ j ∈ J, ω j*‖y j‖^2) := by
    simp only [g,Finset.sum_product,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hgSum] at h
  simpa only [f,Finset.sum_product,mul_assoc] using h

end Lemniscate
