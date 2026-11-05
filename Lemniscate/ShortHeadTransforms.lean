import Lemniscate.ShortCircleCoordinates

/-! Dimension-independent matrix algebra for finite-rank transformations. -/
namespace Lemniscate
open Complex MeasureTheory Matrix
open scoped ComplexConjugate
variable {N : ℕ}

noncomputable def shortHeadPair (v w : Fin N → ℂ) : ℂ := ∑ i, conj (v i)*w i

noncomputable def shortHeadHouseholderMatrix (e a : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then 1 else 0)-
    (1+shortHeadPair e a)⁻¹*(e i+a i)*conj (e j+a j)

noncomputable def shortHeadNeutralMatrix (e p : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then 1 else 0)+e i*conj (p j-e j)

noncomputable def shortHeadNeutralInvMatrix (e p : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then 1 else 0)-e i*conj (p j-e j)

theorem short_head_householder_mulVec (e a v : Fin N → ℂ) :
    shortHeadHouseholderMatrix e a *ᵥ v = v-
      ((1+shortHeadPair e a)⁻¹*shortHeadPair (e+a) v) • (e+a) := by
  funext i
  simp only [shortHeadHouseholderMatrix, mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, shortHeadPair]
  simp only [Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem short_head_neutral_mulVec (e p v : Fin N → ℂ) :
    shortHeadNeutralMatrix e p *ᵥ v = v+shortHeadPair (p-e) v • e := by
  funext i
  simp only [shortHeadNeutralMatrix, mulVec, dotProduct, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, shortHeadPair, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem short_head_neutral_inv_mulVec (e p v : Fin N → ℂ) :
    shortHeadNeutralInvMatrix e p *ᵥ v = v-shortHeadPair (p-e) v • e := by
  funext i
  simp only [shortHeadNeutralInvMatrix, mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    shortHeadPair, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

variable (T : ℝ) [Fact (0<T)]

theorem circle_short_head_householder (e a v : Fin 15 → ℂ) :
    neutralHouseholderDomain (circleShortHead T e) (circleShortHead T a)
      (circleShortHead T v) = circleShortHead T (shortHeadHouseholderMatrix e a *ᵥ v) := by
  let S := circleShortHead T
  have hadd : circleShortHead T e+circleShortHead T a = circleShortHead T (e+a) :=
    (S.map_add e a).symm
  have hp : inner ℂ ((circleShortHead T e : CircleL2 T)+(circleShortHead T a : CircleL2 T))
      (circleShortHead T v : CircleL2 T) = shortHeadPair (e+a) v := by
    rw [← Submodule.coe_add, hadd, circle_short_head_inner]
    rfl
  rw [neutralHouseholderDomain, circle_short_head_inner, hp, hadd, short_head_householder_mulVec]
  change S v-((1+shortHeadPair e a)⁻¹*shortHeadPair (e+a) v) • S (e+a) =
    S (v-((1+shortHeadPair e a)⁻¹*shortHeadPair (e+a) v) • (e+a))
  rw [map_sub, map_smul]

theorem circle_short_head_neutral_inv (e p v : Fin 15 → ℂ) :
    neutralTransformInvDomain (circleShortHead T e) (circleShortHead T p : CircleL2 T)
      (circleShortHead T v) = circleShortHead T (shortHeadNeutralInvMatrix e p *ᵥ v) := by
  let S := circleShortHead T
  have hsub : circleShortHead T p-circleShortHead T e = circleShortHead T (p-e) :=
    (S.map_sub p e).symm
  have hp : inner ℂ ((circleShortHead T p : CircleL2 T)-(circleShortHead T e : CircleL2 T))
      (circleShortHead T v : CircleL2 T) = shortHeadPair (p-e) v := by
    rw [← Submodule.coe_sub, hsub, circle_short_head_inner]
    rfl
  rw [neutralTransformInvDomain, hp, short_head_neutral_inv_mulVec]
  change S v-shortHeadPair (p-e) v • S e = S (v-shortHeadPair (p-e) v • e)
  rw [map_sub, map_smul]

end Lemniscate
