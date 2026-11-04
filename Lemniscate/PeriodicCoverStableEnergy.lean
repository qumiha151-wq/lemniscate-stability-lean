import Lemniscate.PeriodicCoverStableMetric
import Lemniscate.PeriodicBlochMetricEnergy
import Lemniscate.PeriodicProfileCoverSpectrum

/-! The full covered operator is dissipative in the actual finite Bloch
metric. The adjoint phase condition is imposed only on the zero block;
every nonzero balanced block uses its proved signed Bloch energy estimate.
No norm on higher derivatives of the metric is used. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped BigOperators ComplexConjugate

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

private theorem circle_cover_balanced_inner (M : ℕ) (hM : 0 < M)
    (f g : CircleL2 S) :
    inner ℂ f g = ∑ j : Fin M,
      inner ℂ
        (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f)
        (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) g) := by
  classical
  have hreconstruct := (circle_cover_balanced_reconstruction_parseval T S M hM f).1
  calc
    inner ℂ f g = inner ℂ
        (∑ j : Fin M, circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)
          (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f)) g :=
      congrArg (fun u : CircleL2 S => inner ℂ u g) hreconstruct
    _ = ∑ j : Fin M, inner ℂ
        (circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)
          (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f)) g :=
      sum_inner _ _ _
    _ = _ := Finset.sum_congr rfl
      (fun j _ => circle_cover_embedding_inner T S M hM _ _ g)

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

/-- The previously proved cover rate is an all-function energy bound
on the kernel of the lifted adjoint phase functional, in the genuine L2
isomorphism assembled from the zero, positive and negative Bloch blocks. -/
theorem paper_periodic_cover_stable_energy
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T))
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    let E := circlePeriodicExtension T S M hS
    let Q := E q
    let P := E p
    let V := circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM (ψ:CircleL2 T) hnorm
    let Ψ := circleCoverEmbedding T S M hM 0 (ψ:CircleL2 T)
    ∀ f : circleH4Domain S, inner ℂ Ψ (f:CircleL2 S) = 0 →
      (inner ℂ (V (f:CircleL2 S))
        (V (circleH4Operator S (Q^2) ((2:ℂ) • (Q*P))
          (1-(3:ℂ) • (Q^4)) f))).re ≤
        -(if M = 1 then (21/4:ℝ) else 1/(2*(M:ℝ)^2))*‖V (f:CircleL2 S)‖^2 := by
  classical
  dsimp only
  let E := circlePeriodicExtension T S M hS
  let Q := E q
  let P := E p
  let V := circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
    M hM (ψ:CircleL2 T) hnorm
  let B := circleCoverStableBlocks T q p hq hp he hqreal hpreal hs hc ho hr
    M (ψ:CircleL2 T) hnorm
  let C (j : Fin M) := circleCoverComponent T S M hM (circleCoverBalancedIndex M j)
  let a (j : Fin M) : ℝ := (circleCoverBalancedIndex M j:ℝ)/(M:ℝ)
  let gM : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
  let A := circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hQ : HasCircleDeriv S Q P :=
    circle_periodic_extension_deriv T S M hS q p hq
  have hP : HasCircleDeriv S P (-(Q^3)) := by
    simpa only [Q,map_neg,map_pow] using
      circle_periodic_extension_deriv T S M hS _ _ hp
  have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 :=
    fun x => he (circleCoverProjection T S M hS x)
  have hMZ : (M:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hmulti (n : ℤ) :
      fourierCoeff (Q^2 : C(AddCircle S, ℂ)) ((M:ℤ)*n) =
        fourierCoeff (q^2 : C(AddCircle T, ℂ)) n := by
    have h := circle_periodic_extension_fourier T S M hM hS (q^2) ((M:ℤ)*n)
    simpa [E,Q,map_pow,Int.mul_ediv_cancel_left _ hMZ] using h
  have hvanish (n : ℤ) (hn : ¬(M:ℤ) ∣ n) :
      fourierCoeff (Q^2 : C(AddCircle S, ℂ)) n = 0 := by
    have h := circle_periodic_extension_fourier T S M hM hS (q^2) n
    simpa only [if_neg hn,map_pow] using h
  have hV (u : CircleL2 S) (j : Fin M) : C j (V u) = B j (C j u) :=
    circle_cover_balanced_block_equiv_component T S M hM B u j
  have hrate0 : gM ≤ 21/4 := by
    by_cases hM1 : M = 1
    · simp only [gM,if_pos hM1,le_refl]
    · have hMone : (1:ℝ) ≤ M := by exact_mod_cast (Nat.succ_le_iff.mpr hM)
      have hden : (2:ℝ) ≤ 2*(M:ℝ)^2 := by
        nlinarith only [hMone,sq_nonneg ((M:ℝ)-1)]
      have hbound := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hden
      dsimp only [gM]
      rw [if_neg hM1]
      exact hbound.trans (by norm_num)
  intro f hf
  let x (j : Fin M) :=
    circleCoverComponentH4 T S M hM hS (circleCoverBalancedIndex M j) f
  have hAx (j : Fin M) : C j (A f) =
      circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) (a j) (x j) :=
    circle_cover_operator_intertwine T S M hM hS _ _ _ _ _ _
      (circle_profile_square_deriv T q p hq)
      (circle_profile_square_second T q p hq hp he)
      (circle_profile_square_deriv S Q P hQ)
      (circle_profile_square_second S Q P hQ hP hE)
      hmulti hvanish (circleCoverBalancedIndex M j) f
  have hphase : inner ℂ (ψ:CircleL2 T) (circleCoverComponent T S M hM 0
      (f:CircleL2 S)) = 0 := by
    rw [← circle_cover_embedding_inner T S M hM 0 (ψ:CircleL2 T) (f:CircleL2 S)]
    exact hf
  have hblock (j : Fin M) :
      (inner ℂ (B j (C j (f:CircleL2 S))) (B j (C j (A f)))).re ≤
        -gM*‖B j (C j (f:CircleL2 S))‖^2 := by
    by_cases hj : j.val = 0
    · have hindex : circleCoverBalancedIndex M j = 0 := by
        simp only [circleCoverBalancedIndex,hj,Nat.mul_zero,Nat.zero_le,if_true,Int.natCast_zero]
      have ha : a j = 0 := by simp only [a,hindex,Int.cast_zero,zero_div]
      have hBj (u : CircleL2 T) : B j u =
          neutralTransform (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T) u := by
        dsimp only [B,circleCoverStableBlocks]
        rw [if_pos hj]
        rfl
      have hxphase : inner ℂ (ψ:CircleL2 T) ((x j):CircleL2 T) = 0 := by
        simpa only [x,circle_cover_component_h4_coe,hindex] using hphase
      have hz := paper_zero_bloch_metric_energy T q p hq hp he hqreal hpreal hs hc ho hr
        (ψ:CircleL2 T) hd (x j) hxphase
      simp only [hBj]
      rw [hAx,ha,circle_bloch_at_zero]
      have hz' : (inner ℂ
          (neutralTransform (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T)
            (C j (f:CircleL2 S)))
          (neutralTransform (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T)
            (circleH4Operator T (q^2) ((2:ℂ) • (q*p))
              (1-(3:ℂ) • (q^4)) (x j)))).re ≤
          -(21/4:ℝ)*‖neutralTransform (circleUnitRotationH4 T q p hq hp)
            (ψ:CircleL2 T) (C j (f:CircleL2 S))‖^2 := by
        simpa only [x,circle_cover_component_h4_coe,circle_bloch_at_zero] using hz
      exact hz'.trans (mul_le_mul_of_nonneg_right (neg_le_neg hrate0) (sq_nonneg _))
    · have hM1 : M ≠ 1 := by
        intro h
        have hlt := j.isLt
        omega
      obtain ⟨hhalf,hdist⟩ := circle_cover_balanced_parameter_bounds M hM j
      have hdist' : 1/(M:ℝ) ≤ |a j| := hdist hj
      have hapos : 0 ≤ 1/(M:ℝ) := (one_div_pos.mpr hMr).le
      have hmul := mul_nonneg (sub_nonneg.mpr hdist')
        (add_nonneg (abs_nonneg (a j)) hapos)
      have hsquare : (1/(M:ℝ))^2 ≤ (a j)^2 := by
        nlinarith only [hmul,sq_abs (a j)]
      have hrate : gM ≤ (a j)^2/2 := by
        have hid : 1/(2*(M:ℝ)^2) = (1/(M:ℝ))^2/2 := by
          field_simp [hMr.ne']
          <;> ring
        rw [show gM = 1/(2*(M:ℝ)^2) from if_neg hM1,hid]
        linarith only [hsquare]
      let P₀ := circleCenteredL2Equiv T q p hq hp he hqreal hpreal hs hc ho hr
        (ψ:CircleL2 T) hnorm
      let D : CircleL2 T → CircleL2 T :=
        if 0 ≤ a j then (P₀:CircleL2 T → CircleL2 T)
        else fun u => circleReflect T (P₀ (circleReflect T u))
      have hBj (u : CircleL2 T) : B j u = D u := by
        dsimp only [B,circleCoverStableBlocks]
        rw [if_neg hj]
        by_cases hi : circleCoverBalancedIndex M j < 0
        · have hneg : a j < 0 :=
            div_neg_of_neg_of_pos (by exact_mod_cast hi) hMr
          rw [if_pos hi]
          change circleReflect T (P₀ (circleReflect T u)) = D u
          simp only [D,if_neg (not_le.mpr hneg)]
        · have hnonneg : 0 ≤ a j :=
            div_nonneg (by exact_mod_cast (le_of_not_gt hi)) hMr.le
          rw [if_neg hi]
          change P₀ u = D u
          simp only [D,if_pos hnonneg]
      have hsigned := paper_signed_bloch_metric_energy T q p hq hp he hqreal hpreal
        hs hc ho hr ψ hnorm hzero hd (a j) hhalf (x j)
      have hsigned' : (inner ℂ (D (C j (f:CircleL2 S)))
          (D (C j (A f)))).re ≤ -((a j)^2/2)*‖D (C j (f:CircleL2 S))‖^2 := by
        rw [hAx]
        simpa only [D,P₀,x,circle_cover_component_h4_coe] using hsigned
      simp only [hBj]
      exact hsigned'.trans (mul_le_mul_of_nonneg_right
        (neg_le_neg hrate) (sq_nonneg _))
  have hinner : (inner ℂ (V (f:CircleL2 S)) (V (A f))).re =
      ∑ j : Fin M, (inner ℂ (B j (C j (f:CircleL2 S))) (B j (C j (A f)))).re := by
    calc
      (inner ℂ (V (f:CircleL2 S)) (V (A f))).re =
          (∑ j : Fin M, inner ℂ (C j (V (f:CircleL2 S))) (C j (V (A f)))).re :=
        congrArg Complex.re
          (circle_cover_balanced_inner T S M hM (V (f:CircleL2 S)) (V (A f)))
      _ = ∑ j : Fin M,
          (inner ℂ (C j (V (f:CircleL2 S))) (C j (V (A f)))).re :=
        map_sum Complex.reAddGroupHom _ _
      _ = _ := Finset.sum_congr rfl (fun j _ => by rw [hV,hV])
  have hnorm : ‖V (f:CircleL2 S)‖^2 =
      ∑ j : Fin M, ‖B j (C j (f:CircleL2 S))‖^2 := by
    rw [(circle_cover_balanced_reconstruction_parseval T S M hM (V (f:CircleL2 S))).2]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun u : CircleL2 T => ‖u‖^2) (hV _ j))
  change (inner ℂ (V (f:CircleL2 S)) (V (A f))).re ≤ -gM*‖V (f:CircleL2 S)‖^2
  rw [hinner,hnorm,Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => hblock j)

end Profile
end Lemniscate
