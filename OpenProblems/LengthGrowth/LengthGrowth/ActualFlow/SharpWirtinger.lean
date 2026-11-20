import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! The sharp periodic Poincaré inequality in arclength coordinates. -/
noncomputable section
open MeasureTheory Set
namespace LengthGrowth

theorem periodic_wirtinger {L : ℝ} (hL : 0<L) (f g : ℝ → ℂ) (hper : f L = f 0)
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : Continuous g)
    (hmean : (∫ s in 0..L, f s) = 0) :
    (2*Real.pi)^2 * (∫ s in 0..L, ‖f s‖^2) ≤ L^2 * (∫ s in 0..L, ‖g s‖^2) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  have lp (v : ℝ → ℂ) (hv : Continuous v) : MemLp v 2 (volume.restrict (Ioc 0 L)) := by
    apply (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
    exact ((hv.norm.pow 2).intervalIntegrable 0 L).1
  have point (n : ℤ) : (2*Real.pi)^2 * ‖fourierCoeffOn hL f n‖^2 ≤
      L^2 * ‖fourierCoeffOn hL g n‖^2 := by
    by_cases hn : n=0
    · subst n
      have hz : fourierCoeffOn hL f 0 = 0 := by
        rw [fourierCoeffOn_eq_integral]; simp [hmean]
      rw [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
      positivity
    · have h := fourierCoeffOn_of_hasDerivAt hL hn (fun x _ => hf x) (hg.intervalIntegrable _ _)
      rw [hper,sub_self,mul_zero,zero_sub] at h
      have eqn := congrArg norm h
      simp only [norm_mul,norm_div,norm_one,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_I,mul_one,Complex.norm_intCast,abs_of_pos hL,abs_of_pos Real.pi_pos,
        Complex.ofReal_zero,sub_zero,Complex.norm_ofNat] at eqn
      have hnat : (1:ℝ) ≤ |(n:ℝ)| := by
        exact_mod_cast Int.one_le_abs hn
      have hprod : ‖fourierCoeffOn hL f n‖ * (2*Real.pi*|(n:ℝ)|) =
          L * ‖fourierCoeffOn hL g n‖ := by
        rw [eqn]
        field_simp [Real.pi_ne_zero, (by linarith : |(n:ℝ)| ≠ 0)]
      have hp : (2*Real.pi)*‖fourierCoeffOn hL f n‖ ≤ L*‖fourierCoeffOn hL g n‖ := by
        rw [← hprod]
        nlinarith only [mul_le_mul_of_nonneg_left hnat (show 0 ≤ (2*Real.pi)*‖fourierCoeffOn hL f n‖ by positivity)]
      simpa [mul_pow] using pow_le_pow_left₀ (by positivity) hp 2
  have bound := hasSum_le point
    ((hasSum_sq_fourierCoeffOn hL (lp f hc)).mul_left ((2*Real.pi)^2))
    ((hasSum_sq_fourierCoeffOn hL (lp g hg)).mul_left (L^2))
  simp only [sub_zero, smul_eq_mul] at bound
  apply (le_of_mul_le_mul_left (a:=L⁻¹) _ (inv_pos.mpr hL))
  linarith only [bound,show L⁻¹ * ((2*Real.pi)^2 * (∫ s in 0..L, ‖f s‖^2)) =
        (2*Real.pi)^2 * (L⁻¹ * (∫ s in 0..L, ‖f s‖^2)) by ring,
    show L⁻¹*(L^2*(∫ s in 0..L, ‖g s‖^2))=L^2*(L⁻¹*(∫ s in 0..L, ‖g s‖^2)) by ring]

end LengthGrowth
