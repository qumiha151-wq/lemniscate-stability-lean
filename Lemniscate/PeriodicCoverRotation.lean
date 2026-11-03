import Lemniscate.PeriodicCoverSemisimple
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The explicit rotational mode spans the full kernel on every cover.
The profile ODE supplies its H4 regularity and kernel identity; the zero
Bloch component is exactly the already known single-period rotation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

theorem circle_cover_rotation_component (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (Q P : C(AddCircle S, ℂ)) (hQ : HasCircleDeriv S Q P)
    (hmulti : ∀ n : ℤ, fourierCoeff (Q^2 : C(AddCircle S, ℂ)) ((M:ℤ)*n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n) :
    circleCoverComponent T S M hM 0 (circleContinuousL2 S (Q*P)) =
      circleContinuousL2 T (q*p) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_cover_component_fourier,circle_continuous_l2_fourier,circle_continuous_l2_fourier]
  simp only [circleCoverIndex,add_zero]
  have hfreq : circleFrequencyFactor S ((M:ℤ)*n) = circleFrequencyFactor T n := by
    simpa [circleCoverIndex] using circle_cover_frequency T S M hM hS 0 n
  have hL := fourierCoeff_classical_deriv S _ _ (circle_profile_square_deriv S Q P hQ) ((M:ℤ)*n)
  have hT := fourierCoeff_classical_deriv T _ _ (circle_profile_square_deriv T q p hq) n
  rw [circle_continuous_fourier_smul,hmulti,hfreq] at hL
  rw [circle_continuous_fourier_smul] at hT
  linear_combination (1/2:ℂ)*hL-(1/2:ℂ)*hT

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
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (Q P : C(AddCircle S, ℂ))
    (hQ : HasCircleDeriv S Q P) (hP : HasCircleDeriv S P (-(Q^3)))
    (hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1)
    (hmulti : ∀ n : ℤ, fourierCoeff (Q^2 : C(AddCircle S, ℂ)) ((M:ℤ)*n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff (Q^2 : C(AddCircle S, ℂ)) n = 0)
include hq hp he hqreal hpreal hs hc ho hr hM hS hQ hP hE hmulti hvanish

private theorem cover_kernel_coordinates (f : circleH4Domain S)
    (hf : circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) f = 0) :
    ∃ c : ℂ, (f:CircleL2 S) = c • circleContinuousL2 S (Q*P) := by
  let g := circleCoverComponentH4 T S M hM hS 0 f
  have hgker : circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) g = 0 := by
    have h := congrArg (circleCoverComponent T S M hM 0) hf
    rw [circle_cover_operator_intertwine T S M hM hS _ _ _ _ _ _
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      (circle_profile_square_deriv S Q P hQ) (circle_profile_square_second S Q P hQ hP hE)
      hmulti hvanish] at h
    simpa only [g,Int.cast_zero,zero_div,circle_bloch_at_zero,map_zero] using h
  obtain ⟨c,hc₀⟩ := paper_single_period_kernel T q p hq hp he hqreal hpreal hs hc ho hr g hgker
  let R := circleRotationH4 S Q P hQ hP
  have hRcoe : (R:CircleL2 S) = circleContinuousL2 S (Q*P) := rfl
  have hRker : circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) R = 0 :=
    circle_rotation_h4_kernel S Q P hQ hP hE
  let v := f-c • R
  have hvker : circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) v = 0 := by
    simp only [v,map_sub,map_smul,hRker,hf,smul_zero,sub_zero]
  have hCv : circleCoverComponent T S M hM 0 (v:CircleL2 S) = 0 := by
    simp only [v,Submodule.coe_sub,Submodule.coe_smul_of_tower,map_sub,map_smul,hRcoe,
      circle_cover_rotation_component T S M hM hS q p hq Q P hQ hmulti]
    change (g:CircleL2 T)-c • circleContinuousL2 T (q*p) = 0
    rw [hc₀,sub_self]
  have hvzero := paper_cover_kernel_zero_of_zero_component T S q p hq hp he hqreal hpreal hs hc ho hr
    M hM hS _ _ _ (circle_profile_square_deriv S Q P hQ) (circle_profile_square_second S Q P hQ hP hE)
    hmulti hvanish v hvker hCv
  refine ⟨c,?_⟩
  change (f:CircleL2 S)-c • circleContinuousL2 S (Q*P) = 0 at hvzero
  exact sub_eq_zero.mp hvzero

theorem paper_cover_kernel :
    LinearMap.ker (circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))) =
      Submodule.span ℂ {circleRotationH4 S Q P hQ hP} := by
  apply le_antisymm
  · intro f hf
    obtain ⟨c,hc₀⟩ := cover_kernel_coordinates T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM hS Q P hQ hP hE hmulti hvanish f hf
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    apply Subtype.ext
    exact hc₀.symm
  · apply Submodule.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact circle_rotation_h4_kernel S Q P hQ hP hE

omit hp he hqreal hpreal hr hP hE hvanish in
theorem paper_cover_rotation_ne_zero : circleContinuousL2 S (Q*P) ≠ 0 := by
  intro hz
  have h := congrArg (circleCoverComponent T S M hM 0) hz
  rw [circle_cover_rotation_component T S M hM hS q p hq Q P hQ hmulti,map_zero] at h
  exact circle_profile_rotation_ne_zero T q p hq hs hc ho h

theorem paper_cover_kernel_finrank :
    Module.finrank ℂ (LinearMap.ker
      (circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)))) = 1 := by
  rw [paper_cover_kernel T S q p hq hp he hqreal hpreal hs hc ho hr
    M hM hS Q P hQ hP hE hmulti hvanish]
  apply finrank_span_singleton
  intro hz
  have h := congrArg (fun u : circleH4Domain S => (u:CircleL2 S)) hz
  exact paper_cover_rotation_ne_zero T S q p hq hs hc ho M hM hS Q P hQ hmulti h

omit hp he hqreal hpreal hr hvanish in
theorem paper_cover_zero_mem_spectrum :
    (0:ℂ) ∈ circleSpectrum S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) := by
  apply (circle_spectrum_iff_eigenvector S _ _ _ 0).mpr
  refine ⟨circleRotationH4 S Q P hQ hP,?_,?_⟩
  · exact paper_cover_rotation_ne_zero T S q p hq hs hc ho M hM hS Q P hQ hmulti
  · rw [circle_rotation_h4_kernel S Q P hQ hP hE,zero_smul]

end Profile
end Lemniscate
