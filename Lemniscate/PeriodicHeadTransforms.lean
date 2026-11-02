import Lemniscate.PeriodicFiniteCoordinates
import Mathlib.Data.Matrix.Mul

/-! Matrices of the finite changes of variables in the ordinary Fourier basis.
All identities are for the actual H4 or L2 functions. Development source. -/
namespace Lemniscate
open Complex MeasureTheory Matrix
open scoped ComplexConjugate

noncomputable def headPair (v w : Fin 31 → ℂ) : ℂ := ∑ i, conj (v i)*w i

noncomputable def headHouseholderMatrix (e a : Fin 31 → ℂ) : Matrix (Fin 31) (Fin 31) ℂ :=
  fun i j => (if i = j then 1 else 0)-
    (1+headPair e a)⁻¹*(e i+a i)*conj (e j+a j)

noncomputable def headNeutralMatrix (e p : Fin 31 → ℂ) : Matrix (Fin 31) (Fin 31) ℂ :=
  fun i j => (if i = j then 1 else 0)+e i*conj (p j-e j)

noncomputable def headNeutralInvMatrix (e p : Fin 31 → ℂ) : Matrix (Fin 31) (Fin 31) ℂ :=
  fun i j => (if i = j then 1 else 0)-e i*conj (p j-e j)

theorem head_householder_mulVec (e a v : Fin 31 → ℂ) :
    headHouseholderMatrix e a *ᵥ v = v-
      ((1+headPair e a)⁻¹*headPair (e+a) v) • (e+a) := by
  funext i
  simp only [headHouseholderMatrix, mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, headPair]
  simp only [Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem head_neutral_mulVec (e p v : Fin 31 → ℂ) :
    headNeutralMatrix e p *ᵥ v = v+headPair (p-e) v • e := by
  funext i
  simp only [headNeutralMatrix, mulVec, dotProduct, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, headPair, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem head_neutral_inv_mulVec (e p v : Fin 31 → ℂ) :
    headNeutralInvMatrix e p *ᵥ v = v-headPair (p-e) v • e := by
  funext i
  simp only [headNeutralInvMatrix, mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    headPair, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenHeadLinearMap : (Fin 31 → ℂ) →ₗ[ℂ] circleH4Domain T where
  toFun := circleEvenHeadH4 T
  map_add' v w := by
    simp only [circleEvenHeadH4, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [circleEvenHeadH4, Pi.smul_apply, Finset.smul_sum, smul_smul,
      smul_eq_mul, RingHom.id_apply]

theorem circle_even_head_pairing (v : Fin 31 → ℂ) (f : CircleL2 T) :
    inner ℂ (circleEvenHeadH4 T v : CircleL2 T) f =
      headPair v (fun i => fourierCoeff f (evenHeadFrequency i)) := by
  have hb (n : ℤ) : inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n := by
    simpa only [HilbertBasis.repr_apply_apply] using fourierBasis_repr f n
  rw [circle_even_head_h4_coe]
  simp only [sum_inner, inner_smul_left, hb, headPair]

theorem circle_even_head_householder (e a v : Fin 31 → ℂ) :
    neutralHouseholderDomain (circleEvenHeadH4 T e) (circleEvenHeadH4 T a)
      (circleEvenHeadH4 T v) = circleEvenHeadH4 T (headHouseholderMatrix e a *ᵥ v) := by
  let S := circleEvenHeadLinearMap T
  have hadd : circleEvenHeadH4 T e+circleEvenHeadH4 T a = circleEvenHeadH4 T (e+a) :=
    (S.map_add e a).symm
  have hp : inner ℂ ((circleEvenHeadH4 T e : CircleL2 T)+(circleEvenHeadH4 T a : CircleL2 T))
      (circleEvenHeadH4 T v : CircleL2 T) = headPair (e+a) v := by
    rw [← Submodule.coe_add, hadd, circle_even_head_inner]
    rfl
  rw [neutralHouseholderDomain, circle_even_head_inner, hp, hadd, head_householder_mulVec]
  change S v-((1+headPair e a)⁻¹*headPair (e+a) v) • S (e+a) =
    S (v-((1+headPair e a)⁻¹*headPair (e+a) v) • (e+a))
  rw [map_sub, map_smul]

theorem circle_even_head_neutral_inv (e p v : Fin 31 → ℂ) :
    neutralTransformInvDomain (circleEvenHeadH4 T e) (circleEvenHeadH4 T p : CircleL2 T)
      (circleEvenHeadH4 T v) = circleEvenHeadH4 T (headNeutralInvMatrix e p *ᵥ v) := by
  let S := circleEvenHeadLinearMap T
  have hsub : circleEvenHeadH4 T p-circleEvenHeadH4 T e = circleEvenHeadH4 T (p-e) :=
    (S.map_sub p e).symm
  have hp : inner ℂ ((circleEvenHeadH4 T p : CircleL2 T)-(circleEvenHeadH4 T e : CircleL2 T))
      (circleEvenHeadH4 T v : CircleL2 T) = headPair (p-e) v := by
    rw [← Submodule.coe_sub, hsub, circle_even_head_inner]
    rfl
  rw [neutralTransformInvDomain, hp, head_neutral_inv_mulVec]
  change S v-headPair (p-e) v • S e = S (v-headPair (p-e) v • e)
  rw [map_sub, map_smul]

end Lemniscate
