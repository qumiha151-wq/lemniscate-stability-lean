import Lemniscate.ActualLengthNormalization
import Lemniscate.LemniscateStabilityStatement
import Lemniscate.BernoulliReferenceNormalGraph

/-! Actual-length normalization of the proved geometric convergence packet.
All covers, the original scale, quantitative estimates and the original
limiting rotation and parameter changes are retained. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set Filter
open scoped ContDiff Topology

private theorem reference_arclength_geometry
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0 : ℝ)..u, Real.sqrt 2 * ‖bernoulliVelocity t‖)
    (M : ℕ) (hM : 0 < M) :
    0 < lemniscateLength M ∧ ContDiff ℝ ∞ (lemniscateReference e) ∧
    Function.Periodic (lemniscateReference e) (lemniscateLength M) ∧
    ∀ s, ‖deriv (lemniscateReference e) s‖ = 1 := by
  let c : ℝ := Real.sqrt 2
  have hc : 0 < c := Real.sqrt_pos.mpr (by norm_num)
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let B : ℝ → ℂ := fun x => (c : ℂ) * bernoulliCurve (e.symm x)
  obtain ⟨hB, hBper, _, _⟩ := actual_bernoulli_reference_geometry e he
  change ContDiff ℝ ∞ B at hB
  change Function.Periodic B (e (2 * Real.pi)) at hBper
  have he₀ : e 0 = 0 := by rw [he, intervalIntegral.integral_same]
  have hT : 0 < e (2 * Real.pi) := by
    simpa only [he₀] using e.strictMono (by positivity : (0 : ℝ) < 2 * Real.pi)
  have hlength : e (2 * Real.pi) = 4 * Khalf := by
    rw [he, intervalIntegral.integral_const_mul, bernoulli_reference_length]
    field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  have hQ : lemniscateLength M = (M : ℝ) * e (2 * Real.pi) / c := by
    rw [hlength]
    unfold lemniscateLength c
    ring
  have hQpos : 0 < lemniscateLength M := by
    rw [hQ]
    exact div_pos (mul_pos (Nat.cast_pos.mpr hM) hT) hc
  have hreference : lemniscateReference e = fun s => B (c * s) / (c : ℂ) := by
    funext s
    dsimp only [lemniscateReference, B, c]
    field_simp [show (Real.sqrt 2 : ℂ) ≠ 0 from hcC]
  have hregular : ContDiff ℝ ∞ (lemniscateReference e) := by
    rw [hreference]
    have hcomp : ContDiff ℝ ∞ (fun s => B (c * s)) :=
      ContDiff.comp (g := B) (f := fun s : ℝ => c * s) hB
        (contDiff_const.mul contDiff_id)
    exact hcomp.div_const (c : ℂ)
  have hcover : Function.Periodic B ((M : ℝ) * e (2 * Real.pi)) := by
    simpa only [nsmul_eq_mul] using hBper.nsmul M
  have hperiod : Function.Periodic (lemniscateReference e) (lemniscateLength M) := by
    rw [hreference]
    intro s
    change B (c * (s + lemniscateLength M)) / (c : ℂ) = B (c * s) / (c : ℂ)
    have harg : c * (s + lemniscateLength M) = c * s + (M : ℝ) * e (2 * Real.pi) := by
      rw [hQ]
      field_simp [hc.ne']
      <;> ring
    rw [harg, hcover (c * s)]
  refine ⟨hQpos, hregular, hperiod, ?_⟩
  intro s
  have hframe := bernoulli_arclength_frame e he s
  have hd : HasDerivAt (lemniscateReference e)
      (bernoulliVelocity (e.symm (Real.sqrt 2 * s)) /
        (‖bernoulliVelocity (e.symm (Real.sqrt 2 * s))‖ : ℂ)) s := by
    simpa only [lemniscateReference, Function.comp_def] using! hframe.1
  rw [hd.deriv]
  exact hframe.2.1

/-- The actual M-fold Bernoulli reference, with the same fixed rotation and
circle lifts, also gives convergence after division by the evolving length. -/
theorem lemniscate_actual_length_normalization
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0 : ℝ)..u, Real.sqrt 2 * ‖bernoulliVelocity t‖)
    (M : ℕ) (hM : 0 < M) (R : ℂ) (hR : ‖R‖ = 1)
    (Y : ℝ → ℝ → ℂ)
    (hY : ∀ t, 0 ≤ t → ContDiff ℝ ∞ (Y t) ∧ Function.Periodic (Y t) (2 * Real.pi))
    (χ : ℝ → (ℝ ≃o ℝ))
    (hχ : ∀ t, 0 ≤ t → ContDiff ℝ ∞ (χ t : ℝ → ℝ) ∧
      ContDiff ℝ ∞ ((χ t).symm : ℝ → ℝ) ∧
        ∀ s, χ t (s + lemniscateLength M) = χ t s + 2 * Real.pi)
    (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t)
    (hconv : ∀ j : ℕ, Tendsto (fun t => periodicCjNorm j
      (fun s => Y t (χ t s) / (ρ t : ℂ) - R * lemniscateReference e s)) atTop (𝓝 0)) :
    Tendsto (fun t => periodicCurveLength (2 * Real.pi) (Y t) / ρ t)
      atTop (𝓝 (lemniscateLength M)) ∧
    ∀ j : ℕ, Tendsto (fun t => periodicCjNorm j
      (fun s => Y t (χ t s) / (periodicCurveLength (2 * Real.pi) (Y t) : ℂ) -
        R * lemniscateReference e s / (lemniscateLength M : ℂ))) atTop (𝓝 0) := by
  obtain ⟨hL, hβ, hp, hu⟩ := reference_arclength_geometry e he M hM
  exact periodic_actual_length_normalization (2 * Real.pi) (lemniscateLength M) hL
    (lemniscateReference e) hβ hp hu R hR Y hY χ hχ ρ hρ hconv

/-- Strengthening the existing convergence packet by actual-length
normalization keeps every original quantitative field and exactly the same
translation, limiting rotation and family of parameter changes. -/
theorem lemniscate_convergence_actual_length
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0 : ℝ)..u, Real.sqrt 2 * ‖bernoulliVelocity t‖)
    (M : ℕ) (hM : 0 < M) (γ₀ : ℝ → ℂ) (Y : ℝ → ℝ → ℂ)
    (εRate CRate : Ioo (0 : ℝ) (lemniscateGap M) → ℕ → ℝ)
    (hY : ∀ t, 0 ≤ t → ContDiff ℝ ∞ (Y t) ∧ Function.Periodic (Y t) (2 * Real.pi))
    (hconv : LemniscateScaledConvergence e M γ₀ Y εRate CRate) :
    LemniscateConvergence e M γ₀ Y εRate CRate := by
  dsimp only [LemniscateScaledConvergence] at hconv
  obtain ⟨ha, p₀, R, hR, χ, hχ, hcj, hbase, hquant⟩ := hconv
  obtain ⟨hlength, hactual⟩ := lemniscate_actual_length_normalization e he M hM R hR Y hY χ hχ
    (fun t => (lemniscateInitialScale M γ₀ ^ 4 + 30 * t) ^ (1 / 4 : ℝ))
    (fun t ht => Real.rpow_pos_of_pos (by positivity) _) hcj
  exact ⟨ha, p₀, R, hR, χ, hχ, hcj, hlength, hactual, hbase, hquant⟩

end Lemniscate
