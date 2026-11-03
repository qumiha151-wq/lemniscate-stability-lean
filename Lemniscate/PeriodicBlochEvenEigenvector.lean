import Lemniscate.PeriodicBlochEigenvalueBounds

/-! Transfer the centered energy bound to actual even-frequency eigenvectors.
The exact bounded changes preserve the H4 domain and cannot annihilate a
nonzero eigenvector. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

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

theorem paper_even_bloch_eigenvalue_bound
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2)
    (f : circleH4Domain T) (hfne : (f:CircleL2 T) ≠ 0)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0)
    (w : ℂ) (hAf : circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f =
      w • (f:CircleL2 T)) : w.re ≤ -(1/2:ℝ)*α^2 := by
  obtain ⟨ψ,hnorm,hzero,_,_,hd⟩ :=
    paper_single_period_neutral_decomposition T q p hq hp he hqreal hpreal hs hc ho hr
  let e := circleUnitRotationH4 T q p hq hp
  have hecoe : (e:CircleL2 T) = circleUnitRotation T q p :=
    circle_unit_rotation_h4_coe T q p hq hp
  let v := neutralTransformDomain e (ψ:CircleL2 T) f
  let g := circleRotationHouseholderH4 T q p hq hp v
  have hv : (v:CircleL2 T) = neutralTransform e (ψ:CircleL2 T) (f:CircleL2 T) := rfl
  have hg : (g:CircleL2 T) = circleRotationHouseholder T q p (v:CircleL2 T) :=
    circle_rotation_householder_h4_coe T q p hq hp v
  have hginv : circleRotationHouseholderH4 T q p hq hp g = v :=
    paper_householder_h4_involutive T q p hq hp he hqreal hpreal hs hc ho hr v
  have hvinv : neutralTransformInvDomain e (ψ:CircleL2 T) v = f := (hd.2.1 f).2
  have hgeig : circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α g =
      w • (g:CircleL2 T) := by
    unfold circleCenteredBlochOperator
    rw [hginv,hvinv,hAf,map_smul,map_smul,← hv,← hg]
  have hgne : (g:CircleL2 T) ≠ 0 := by
    intro hz
    have hvzero : (v:CircleL2 T) = 0 := by
      have h := congrArg (circleRotationHouseholder T q p) hz
      rw [hg,paper_householder_involutive T q p hq hp he hqreal hpreal hs hc ho hr,map_zero] at h
      exact h
    have h := (hd.1 (f:CircleL2 T)).2
    rw [← hv,hvzero,map_zero] at h
    exact hfne h.symm
  have hgeven : ∀ n : ℤ, Odd n → fourierCoeff (g:CircleL2 T) n = 0 := by
    intro n hn
    obtain ⟨i,hi⟩ := (odd_frequency_range n).mpr hn
    rw [← hi,hg]
    apply circle_rotation_householder_no_odd T q p hq ho
    intro k
    change fourierCoeff ((f:CircleL2 T)+inner ℂ ((ψ:CircleL2 T)-(e:CircleL2 T))
      (f:CircleL2 T) • (e:CircleL2 T)) (2*k+1) = 0
    rw [circle_fourierCoeff_add,circle_fourierCoeff_smul,
      hf (2*k+1) (by exact ⟨k,by ring⟩),hecoe,circle_unit_rotation_no_odd T q p hq ho]
    ring
  exact paper_centered_even_eigenvalue_bound T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hnorm hzero hd α hα0 hαhalf g hgne hgeven w hgeig

end Profile
end Lemniscate
