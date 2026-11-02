import Lemniscate.PeriodicCoverEmbeddingOperator
import Lemniscate.PeriodicProfileAnalyticEigenpair
import Lemniscate.PeriodicCoverSpectralBound
import Lemniscate.PeriodicSpectralGap
import Lemniscate.PeriodicCoverExtension
import Mathlib.Analysis.SpecificLimits.Basic

/-! An actual nonzero eigenvalue of each sufficiently large cover lies at
distance O(M^-2) from zero. The constants are chosen before the covering
number and long period. All coefficients are the natural periodic extensions;
their derivative, reality and Fourier extension properties are proved. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped ComplexConjugate Topology
variable (T : ℝ) [Fact (0 < T)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
include hq hp he hqreal hpreal hs hc ho hr

theorem paper_cover_sharp_gap_bounds :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M →
      ∀ (S : ℝ) [Fact (0 < S)] (hS : S = (M:ℝ)*T),
        let E := circlePeriodicExtension T S M hS
        let H := E (q^2)
        let H₁ := E ((2:ℂ) • (q*p))
        let H₂ := E (1-(3:ℂ) • (q^4))
        ∃ w : ℂ, w ∈ circleSpectrum S H H₁ H₂ ∧ w ≠ 0 ∧
          -(K/(M:ℝ)^2) ≤ w.re ∧ w.re ≤ -(1/(2*(M:ℝ)^2)) ∧
          1/(2*(M:ℝ)^2) ≤ circleSpectralGap S H H₁ H₂ ∧
          circleSpectralGap S H H₁ H₂ ≤ K/(M:ℝ)^2 := by
  obtain ⟨ψ,μ,g,hμ,hg,hμ0,hg0,heven,⟨K,hK,hquad⟩,hnorm,heig⟩ :=
    paper_analytic_bloch_eigenpair_exists T q p hq hp he hqreal hpreal hs hc ho hr
  have tR : Tendsto (fun M : ℕ => 1/(M:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hcast : Tendsto (fun α : ℝ => (α:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have tC : Tendsto (fun M : ℕ => ((1/(M:ℝ):ℝ):ℂ)) atTop (𝓝 (0:ℂ)) := hcast.comp tR
  have hcombined := Filter.Eventually.and (tC.eventually hquad)
    (Filter.Eventually.and (tC.eventually hnorm) (tR.eventually heig))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hcombined
  refine ⟨K,hK,max 2 N,le_max_left 2 N,?_⟩
  intro M hMN S instS hS
  let E := circlePeriodicExtension T S M hS
  let H := E (q^2)
  let H₁ := E ((2:ℂ) • (q*p))
  let H₂ := E (1-(3:ℂ) • (q^4))
  have hM2 : 2 ≤ M := le_trans (le_max_left 2 N) hMN
  have hM : 0 < M := by omega
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  obtain ⟨hquadM,hnormM,heigM⟩ := hN M (le_trans (le_max_right 2 N) hMN)
  obtain ⟨u,hu,hAu⟩ := heigM
  let w : ℂ := μ ((1/(M:ℝ):ℝ):ℂ)
  have hune : (u:CircleL2 T) ≠ 0 := by rw [hu]; exact hnormM.2
  have hAu' : circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) (1/(M:ℝ)) u = w • (u:CircleL2 T) :=
    hAu.trans (congrArg (fun v : CircleL2 T => w • v) hu.symm)
  have hj : 2*|(1:ℤ)| ≤ (M:ℤ) := by
    norm_num only [abs_one,mul_one]
    exact_mod_cast hM2
  have hα : |1/(M:ℝ)| ≤ 1/2 := by
    simpa only [Int.cast_one] using circle_cover_parameter_bound M hM 1 hj
  have hwshort := (paper_bloch_spectrum_iff_eigenvector T q p he hqreal hpreal hr
    (1/(M:ℝ)) hα w).mpr ⟨u,hune,hAu'⟩
  have hb := paper_uniform_bloch_spectral_bound T q p hq hp he hqreal hpreal hs hc ho hr
    (1/(M:ℝ)) hα w hwshort
  have hupper : w.re ≤ -(1/(2*(M:ℝ)^2)) := by
    calc
      w.re ≤ -(1/2:ℝ)*(1/(M:ℝ))^2 := hb
      _ = _ := by field_simp [ne_of_gt hMr]
  have hwne : w ≠ 0 := by
    intro hz
    rw [hz,Complex.zero_re] at hupper
    have hpos : 0 < 1/(2*(M:ℝ)^2) := by positivity
    linarith
  have hscale : K*‖((1/(M:ℝ):ℝ):ℂ)‖^2 = K/(M:ℝ)^2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,one_pow]
    ring
  have hnormw : ‖w‖ ≤ K/(M:ℝ)^2 := by rw [← hscale]; exact hquadM
  have hlower : -(K/(M:ℝ)^2) ≤ w.re :=
    le_trans (neg_le_neg hnormw) ((abs_le.mp (Complex.abs_re_le_norm w)).1)
  have h0real : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow,hqreal]
  have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul,map_ofNat,hqreal,hpreal]
  have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub,map_mul,map_one,map_ofNat,map_pow,hqreal]
  have hD : HasCircleDeriv S H H₁ := circle_periodic_extension_deriv T S M hS _ _
    (circle_profile_square_deriv T q p hq)
  have hD₁ : HasCircleDeriv S H₁ H₂ := circle_periodic_extension_deriv T S M hS _ _
    (circle_profile_square_second T q p hq hp he)
  have Hreal := circle_periodic_extension_real T S M hS _ h0real
  have H₁real := circle_periodic_extension_real T S M hS _ h1real
  have H₂real := circle_periodic_extension_real T S M hS _ h2real
  have hMZ : (M:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hmulti (n : ℤ) : fourierCoeff H ((M:ℤ)*n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n := by
    rw [circle_periodic_extension_fourier T S M hM hS]
    simp [Int.mul_ediv_cancel_left _ hMZ]
  have hvanish (n : ℤ) (hn : ¬(M:ℤ) ∣ n) : fourierCoeff H n = 0 := by
    rw [circle_periodic_extension_fourier T S M hM hS]
    exact if_neg hn
  let v := circleCoverEmbeddingH4 T S M hM hS 1 u
  have hvne : (v:CircleL2 S) ≠ 0 := by
    intro hz
    have hc0 := congrArg (circleCoverComponent T S M hM 1) hz
    have hu0 : (u:CircleL2 T) = 0 := by
      simpa only [v,circle_cover_embedding_h4_coe,circle_cover_component_embedding,map_zero] using hc0
    exact hune hu0
  have hAv : circleH4Operator S H H₁ H₂ v = w • (v:CircleL2 S) := by
    have hlift := circle_cover_embedding_operator T S M hM hS
      (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) H H₁ H₂
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      hD hD₁ h0real h1real h2real Hreal H₁real H₂real hmulti hvanish 1 u
    simpa only [v,Int.cast_one,hAu',map_smul,circle_cover_embedding_h4_coe] using hlift
  have hwspec := (circle_spectrum_iff_eigenvector S H H₁ H₂ w).mpr ⟨v,hvne,hAv⟩
  have hM1 : M ≠ 1 := by omega
  have hgap := circle_spectral_gap_bounds S H H₁ H₂ (1/(2*(M:ℝ)^2)) (K/(M:ℝ)^2)
    (fun z hz hzne => by
      simpa only [if_neg hM1] using paper_cover_nonzero_spectral_bound T S q p hq hp he hqreal hpreal
        hs hc ho hr M hM hS H H₁ H₂ hD hD₁ hmulti hvanish z hzne hz)
    w hwspec hwne hlower
  exact ⟨w,hwspec,hwne,hlower,hupper,hgap⟩

end Profile
end Lemniscate
