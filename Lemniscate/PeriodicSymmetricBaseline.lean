import Lemniscate.PeriodicSymmetricHighRows
import Lemniscate.PeriodicHighFourierNorm
import Lemniscate.FiniteEnergyCertificate

/-! Turn the actual weighted matrix bound into the high H^{-2} estimate
for every finite low-frequency vector. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

private theorem weighted_complex_sum_square {ι : Type*} [Fintype ι]
    (a v : ι → ℂ) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ‖∑ i, v i*a i‖^2 ≤ (∑ i, ‖a i‖^2/δ i)*(∑ i, δ i*‖v i‖^2) := by
  classical
  have h := finite_weighted_coupling Finset.univ ({()}:Finset Unit)
    (fun i _ => a i) δ (fun _ => 1) (fun i => conj (v i)) (fun _ => 1)
    (fun i _ => hδ i) (fun _ _ => by norm_num)
  simpa only [Finset.sum_singleton,Complex.conj_conj,mul_one,norm_one,one_pow,
    one_mul,Complex.norm_conj] using h

variable (T : ℝ) [Fact (0 < T)]

theorem circle_symmetric_baseline_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25) (v : Fin 31 → ℂ) :
    (∑ j : Fin 3, ∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j (circleEvenHeadH4 T v)) n‖^2/
        (n:ℝ)^4 else 0) ≤ (1/9)*(∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2) := by
  classical
  let δ (i : Fin 31) : ℝ := (evenFactorPenalty i:ℝ)
  let E : ℝ := ∑ i : Fin 31, δ i*‖v i‖^2
  let S : Set ℤ := {n | Even n ∧ 32 ≤ |(n:ℝ)|}
  let g (j : Fin 3) := circleBlochSymmetricCoefficient T h h₁ h₂ j (circleEvenHeadH4 T v)
  let B (j : Fin 3) (i : Fin 31) (n : ℤ) := fourierCoeff
    (circleBlochSymmetricCoefficient T h h₁ h₂ j (circleFourierH4 T (evenHeadFrequency i))) n
  let F (j : Fin 3) (n : ℤ) : ℝ := if n ∈ S then ‖fourierCoeff (g j) n‖^2/(n:ℝ)^4 else 0
  let R (i : Fin 31) (n : ℤ) : ℝ := if n ∈ S then
    ∑ j : Fin 3, ‖B j i n‖^2/(δ i*(n:ℝ)^4) else 0
  have hδ (i : Fin 31) : 0 < δ i := by
    dsimp only [δ]
    rw [even_factor_penalty_values i]
    exact Rat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℚ) < 1/16) (even_mode_penalty_lower _))
  have hE : 0 ≤ E := Finset.sum_nonneg (fun i _ => mul_nonneg (hδ i).le (sq_nonneg _))
  have hS (n : ℤ) (hn : n ∈ S) : 32 ≤ |(n:ℝ)| := hn.2
  have hfourier (j : Fin 3) (n : ℤ) : fourierCoeff (g j) n = ∑ i : Fin 31, v i*B j i n := by
    have hi (f : CircleL2 T) : inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n := by
      rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]
    rw [← hi]
    simp only [g,circleEvenHeadH4,map_sum,map_smul,inner_sum,inner_smul_right]
    simp only [hi,B]
  have hF (j : Fin 3) : Summable (F j) :=
    (circle_high_fourier_square_bound T (g j) S hS).1
  have hR (i : Fin 31) : Summable (R i) := by
    have hi := i.isLt
    have hm : ((i.val:ℤ)-15).natAbs ≤ 15 := by
      have hb : (((i.val:ℤ)-15).natAbs:ℤ) ≤ 15 := by
        rw [Int.natCast_natAbs,abs_le]
        constructor <;> omega
      exact_mod_cast hb
    have heq : R i = circleSymmetricHighRow T h h₁ h₂ ((i.val:ℤ)-15) := by
      funext n
      exact (circle_symmetric_high_head_row T h h₁ h₂ i n).symm
    rw [heq]
    exact (circle_symmetric_high_row_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr _ hm).1
  have hM : (∑ i : Fin 31, ∑' n : ℤ, R i n) < 1/9 :=
    circle_symmetric_baseline_matrix_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
  have hpoint (n : ℤ) : (∑ j : Fin 3, F j n) ≤ E*(∑ i : Fin 31, R i n) := by
    by_cases hn : n ∈ S
    · simp only [F,R,if_pos hn]
      calc
        _ ≤ ∑ j : Fin 3, ((∑ i : Fin 31, ‖B j i n‖^2/δ i)*E)/(n:ℝ)^4 := by
          apply Finset.sum_le_sum
          intro j _
          apply div_le_div_of_nonneg_right _ (by positivity)
          rw [hfourier]
          exact weighted_complex_sum_square (fun i => B j i n) v δ hδ
        _ = _ := by
          simp only [div_eq_mul_inv,mul_inv_rev,Finset.sum_mul,Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    · simp only [F,R,if_neg hn,Finset.sum_const_zero,mul_zero,le_refl]
  have hFS : HasSum (fun n : ℤ => ∑ j : Fin 3, F j n) (∑ j : Fin 3, ∑' n : ℤ, F j n) := by
    apply hasSum_sum
    intro j _
    exact (hF j).hasSum
  have hRS : HasSum (fun n : ℤ => ∑ i : Fin 31, R i n) (∑ i : Fin 31, ∑' n : ℤ, R i n) := by
    apply hasSum_sum
    intro i _
    exact (hR i).hasSum
  have hbound := hFS.summable.tsum_le_tsum hpoint (hRS.summable.mul_left E)
  rw [hFS.tsum_eq,tsum_mul_left,hRS.tsum_eq] at hbound
  change (∑ j : Fin 3, ∑' n : ℤ, F j n) ≤ (1/9)*E
  exact hbound.trans (by nlinarith only [mul_le_mul_of_nonneg_left hM.le hE])

end Lemniscate
