import Lemniscate.PhysicalTime
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The expanding scale and normalized time of the original elastic flow. -/
noncomputable section
namespace Lemniscate
open Filter
open scoped Topology

private theorem normalization_clock_hasDerivAt (a t : ℝ)
    (ha : 0 < a) (ht : 0 ≤ t) :
    HasDerivAt (normalizedTime a) (a^4+30*t)⁻¹ t := by
  have ha4 : a^4 ≠ 0 := pow_ne_zero 4 ha.ne'
  have hb := timeBase_pos a t ha ht
  have hd : HasDerivAt (timeBase a) (30/a^4) t := by
    simpa only [timeBase,id_eq,mul_one] using!
      (((hasDerivAt_id t).const_mul 30).div_const (a^4)).const_add 1
  have hl := (hd.log hb.ne').const_mul (1/30:ℝ)
  convert! hl using 1
  dsimp only [timeBase]
  have hu : a^4+30*t ≠ 0 := ne_of_gt (by positivity : 0<a^4+30*t)
  field_simp [ha4,hu]
  <;> ring

/-- A positive scale with exactly the paper's fourth-root formula has
the required actual derivatives and tends to infinity. The normalized
clock starts at zero and tends to infinity on the same physical axis. -/
theorem physical_normalization (a : ℝ) (ha : 0 < a) :
    ∃ ρ : ℝ → ℝ,
      ρ 0 = a ∧ normalizedTime a 0 = 0 ∧
      (∀ t : ℝ, 0 ≤ t →
        0 < ρ t ∧ ρ t = (a^4+30*t)^(1/4:ℝ) ∧
        0 ≤ normalizedTime a t ∧
        (0 < t → 0 < normalizedTime a t) ∧
        HasDerivAt ρ ((15/2:ℝ)*(ρ t)⁻¹^3) t ∧
        HasDerivAt (normalizedTime a) ((ρ t)⁻¹^4) t) ∧
      Tendsto ρ atTop atTop ∧ Tendsto (normalizedTime a) atTop atTop := by
  let c : ℝ := 15/2
  let ρ : ℝ → ℝ := fun t => a*Real.exp (c*normalizedTime a t)
  have hσ0 : normalizedTime a 0 = 0 := by simp [normalizedTime,timeBase]
  have hρpos (t : ℝ) : 0 < ρ t := mul_pos ha (Real.exp_pos _)
  have hpow (t : ℝ) (ht : 0 ≤ t) : (ρ t)^4 = a^4+30*t := by
    dsimp only [ρ]
    rw [mul_pow,← Real.exp_nat_mul]
    have hexp : (4:ℝ)*(c*normalizedTime a t) = Real.log (timeBase a t) := by
      dsimp only [c,normalizedTime]
      ring
    change a^4*Real.exp ((4:ℝ)*(c*normalizedTime a t))=a^4+30*t
    rw [hexp,Real.exp_log (timeBase_pos a t ha ht)]
    dsimp only [timeBase]
    field_simp [pow_ne_zero 4 ha.ne']
    <;> ring
  have hbaseTop : Tendsto (timeBase a) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop ((b-1)*a^4/30)] with t ht
    have h : b-1 ≤ 30*t/a^4 :=
      (le_div_iff₀ (pow_pos ha 4)).mpr (by nlinarith only [ht])
    dsimp only [timeBase]
    linarith only [h]
  have hσTop : Tendsto (normalizedTime a) atTop atTop := by
    simpa only [normalizedTime,Function.comp_def] using!
      (Real.tendsto_log_atTop.comp hbaseTop).const_mul_atTop
        (by norm_num : (0:ℝ) < 1/30)
  have hρTop : Tendsto ρ atTop atTop := by
    have hc : 0 < c := by norm_num [c]
    simpa only [ρ,Function.comp_def] using!
      (Real.tendsto_exp_atTop.comp (hσTop.const_mul_atTop hc)).const_mul_atTop ha
  refine ⟨ρ,?_,hσ0,?_,hρTop,hσTop⟩
  · simp only [ρ,hσ0,mul_zero,Real.exp_zero,mul_one]
  · intro t ht
    have hr := hρpos t
    have hrne := hr.ne'
    have hroot : ρ t = (a^4+30*t)^(1/4:ℝ) := by
      have hroot4 : ((ρ t)^4:ℝ)^(1/4:ℝ)=ρ t := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hr.le]
        norm_num
      exact hroot4.symm.trans (congrArg (fun z : ℝ => z^(1/4:ℝ)) (hpow t ht))
    have hb1 : 1 ≤ timeBase a t := by
      have hh : 0 ≤ 30*t/a^4 := div_nonneg (by positivity) (pow_pos ha 4).le
      dsimp only [timeBase]
      linarith only [hh]
    have hσnonneg : 0 ≤ normalizedTime a t :=
      mul_nonneg (by norm_num) (Real.log_nonneg hb1)
    have hσpos : 0 < t → 0 < normalizedTime a t := by
      intro htp
      have hh : 0 < 30*t/a^4 := div_pos (by positivity) (pow_pos ha 4)
      have hb : 1 < timeBase a t := by dsimp only [timeBase]; linarith only [hh]
      exact mul_pos (by norm_num) (Real.log_pos hb)
    have hσ := normalization_clock_hasDerivAt a t ha ht
    have hi : (a^4+30*t)⁻¹ = (ρ t)⁻¹^4 := by rw [← hpow t ht,inv_pow]
    have hρ := ((hσ.const_mul c).exp).const_mul a
    have hdρ : HasDerivAt ρ ((15/2:ℝ)*(ρ t)⁻¹^3) t := by
      convert! hρ using 1
      rw [hi]
      change (15/2:ℝ)*(ρ t)⁻¹^3 =
        a*(Real.exp (c*normalizedTime a t)*(c*(ρ t)⁻¹^4))
      calc
        _ = c*(ρ t)*(ρ t)⁻¹^4 := by dsimp only [c]; field_simp [hrne] <;> ring
        _ = _ := by dsimp only [ρ]; ring
    exact ⟨hr,hroot,hσnonneg,hσpos,hdρ,hσ.congr_deriv hi⟩

end Lemniscate
