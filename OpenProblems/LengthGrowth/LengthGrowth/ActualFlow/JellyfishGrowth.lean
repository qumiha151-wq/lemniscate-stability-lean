import LengthGrowth.ActualFlow.GrowthEnvelope
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Length coefficients of the reflected-arc expanders. The shooting
branch and its derivatives are the inputs of the Andrews–Wheeler theorem. -/
noncomputable section
open Filter Set
open scoped Topology
namespace LengthGrowth.JellyfishGrowth

/-- For a pure dilation in the normalisation `V = -(k_ss+k³/2)`,
the fourth power of its asymptotic length coefficient is `4*a*L₀⁴`. -/
theorem homothetic_length_fourth_limit {length : ℝ → ℝ} {a L : ℝ}
    (profile : ∀ t ≥ 0, length t ^ 4 = L^4 * (1+4*a*t)) :
    Tendsto (fun t => length t ^ 4 / t) atTop (𝓝 (4*a*L^4)) := by
  have h := (tendsto_id.const_div_atTop (L^4)).add_const (4*a*L^4)
  simp only [zero_add, id_eq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [profile t ht.le]
  field_simp [ht.ne']

private theorem slope_on_branch {f : ℝ → ℝ} {d : ℝ} {e : ℕ → ℝ}
    (der : HasDerivAt f d 0) (at_zero : f 0 = 0)
    (branch : Tendsto e atTop (𝓝[>] 0)) :
    Tendsto (fun n => f (e n)/e n) atTop (𝓝 d) := by
  simpa [Function.comp_def, at_zero, div_eq_inv_mul] using
    der.tendsto_slope_zero_right.comp branch

/-- The fourth power of the growth coefficient on the one-turn branch,
divided by the square of its symmetry order, tends to a positive explicit
constant when `angle' 0 = Y > 0` and `alpha' 0 = -Y/(2H)`. -/
theorem one_turn_shooting_asymptotic {angle alpha arc : ℝ → ℝ} {e : ℕ → ℝ}
    {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H)
    (angle_zero : angle 0 = 0) (alpha_zero : alpha 0 = 0)
    (angle_der : HasDerivAt angle Y 0) (alpha_der : HasDerivAt alpha (-(Y/(2*H))) 0)
    (arc_cont : ContinuousAt arc 0) (branch : Tendsto e atTop (𝓝[>] 0))
    (seam : ∀ᶠ m in atTop, angle (e m) = Real.pi / (m : ℝ)) :
    Tendsto (fun m => 4 * (-alpha (e m) * e m) * (2*(m : ℝ)*arc (e m))^4 / (m : ℝ)^2)
      atTop (𝓝 (32 * (arc 0)^4 * Real.pi^2 / (Y*H))) := by
  have ha := slope_on_branch alpha_der alpha_zero branch
  have hs := slope_on_branch angle_der angle_zero branch
  have hpos : ∀ᶠ m in atTop, 0 < e m := branch.eventually self_mem_nhdsWithin
  have hme : Tendsto (fun m : ℕ => (m:ℝ)*e m) atTop (𝓝 (Real.pi/Y)) := by
    apply ((tendsto_const_nhds (x := Real.pi)).div hs hY.ne').congr'
    filter_upwards [seam, hpos, eventually_gt_atTop 0] with m hm he hmpos
    have hcast : (0:ℝ) < m := by exact_mod_cast hmpos
    change Real.pi / (angle (e m) / e m) = _
    rw [hm]
    field_simp [he.ne', hcast.ne', Real.pi_ne_zero]
  have hl := arc_cont.tendsto.comp (branch.mono_right nhdsWithin_le_nhds)
  have hc := (((hl.pow 4).mul ha.neg).mul (hme.pow 2)).const_mul 64
  rw [show 32*(arc 0)^4*Real.pi^2/(Y*H) =
    64*((arc 0)^4 * -(-(Y/(2*H))) * (Real.pi/Y)^2) by field_simp; ring]
  apply hc.congr'
  filter_upwards [hpos, eventually_gt_atTop 0] with m he hm
  have hn : (0:ℝ) < m := by exact_mod_cast hm
  change 64 * (arc (e m)^4 * -(alpha (e m)/e m) * ((m:ℝ)*e m)^2) = _
  field_simp [he.ne',hn.ne']
  ring

end LengthGrowth.JellyfishGrowth
