import SolitonClassification.SolitonDilation
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! A bound for the ratio of the rotation and dilation coefficients of a
noncircular actual periodic support profile. -/
noncomputable section
namespace ClosedSimilarity
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false

/-- Centering a periodic primitive at its midrange costs at most a quarter
of its total variation over one period. -/
private lemma centered_primitive_bound {r q : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hd : ∀ s, HasDerivAt r (q s) s) (hq : Continuous q) (he : r L = r 0) :
    ∃ c : ℝ, ∀ s ∈ Icc 0 L, |r s-c| ≤ (∫ t in 0..L, |q t|)/4 := by
  have hr : Continuous r := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have edge (x y : ℝ) (hxy : x ≤ y) :
      |r y-r x| ≤ ∫ t in x..y, |q t| := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hd s) (hq.intervalIntegrable x y)]
    exact intervalIntegral.abs_integral_le_integral_abs hxy
  have ordered (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ L) :
      2 * |r y-r x| ≤ ∫ t in 0..L, |q t| := by
    have hback : |r y-r x| ≤ |r L-r y| + |r x-r 0| := by
      rw [abs_sub_comm (r y) (r x)]
      calc
        |r x-r y| = |(r L-r y)+(r x-r 0)| := by rw [he]; congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hq.abs.intervalIntegrable 0 x) (hq.abs.intervalIntegrable x y)
    have hadd' := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hq.abs.intervalIntegrable 0 y) (hq.abs.intervalIntegrable y L)
    linarith [edge x y hxy, edge 0 x hx, edge y L hy]
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hL.le) hr.continuousOn
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hL.le) hr.continuousOn
  have span : 2 * |r y-r x| ≤ ∫ t in 0..L, |q t| := by
    rcases le_total x y with h | h
    · exact ordered x y hx.1 h hy.2
    · rw [abs_sub_comm]; exact ordered y x hy.1 h hx.2
  have hxy : r x ≤ r y := hmin hy
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at span
  refine ⟨(r x+r y)/2, fun s hs => abs_le.mpr ⟨?_,?_⟩⟩
  · linarith [show r x ≤ r s from hmin hs]
  · linarith [show r s ≤ r y from hmax hs]

namespace PeriodicSupportProfile
variable {a b L : ℝ} (z : PeriodicSupportProfile a b L)

def radiusEnergy (s : ℝ) : ℝ := (z.p s ^ 2 + z.q s ^ 2)/2

theorem radiusEnergy_hasDerivAt (s : ℝ) : HasDerivAt z.radiusEnergy (z.q s) s := by
  convert (((z.dp s).pow 2).add ((z.dq s).pow 2)).div_const 2 using 1 <;>
    first | rfl | ring

theorem radiusEnergy_periodic : Function.Periodic z.radiusEnergy L := by
  intro s
  simp only [radiusEnergy, z.periodic_p s, z.periodic_q s]

lemma tangent_support_square_pos (hL : 0 < L)
    (hn : ¬∃ c, ∀ s, z.k s = c) : 0 < ∫ s in 0..L, z.q s ^ 2 := by
  by_contra! hh
  have hz := le_antisymm hh
    (intervalIntegral.integral_nonneg_of_forall hL.le (fun s => sq_nonneg (z.q s)))
  have hi := continuous_nonneg_zero_of_integral_zero hL (z.continuous_q.pow 2)
    (fun s _ => sq_nonneg _) hz
  have hq (s : ℝ) : z.q s = 0 := by
    obtain ⟨t, ht, he⟩ := z.periodic_q.exists_mem_Ico₀ hL s
    rw [he]
    exact sq_eq_zero_iff.mp (hi t ⟨ht.1, ht.2.le⟩)
  have hp (s : ℝ) : z.p s = z.p 0 := by
    have hd (u : ℝ) : HasDerivAt z.p 0 u := by simpa [hq u] using z.dp u
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := s) (fun u _ => hd u) (continuous_const.intervalIntegrable 0 s)
    exact sub_eq_zero.mp (by simpa using hh.symm)
  have kp (s : ℝ) : 1 + z.k s * z.p 0 = 0 := by
    have h := (z.dq s).deriv.symm
    have hf : z.q = fun _ => 0 := funext hq
    rwa [hf, deriv_const', hp s] at h
  have hpn : z.p 0 ≠ 0 := by intro h; have := kp 0; simp [h] at this
  exact hn ⟨-1 / z.p 0, fun s => (eq_div_iff hpn).mpr (by linarith [kp s])⟩

/-- The primitive combines the rotation stress with a centered radial moment.
Both curvature and radial centering constants are free. -/
theorem centered_pitch_identity (hL : 0 < L) (c h : ℝ) :
    (b/a) * (∫ s in 0..L, z.q s ^ 2) =
      -(∫ s in 0..L, (z.k s-h)*((z.radiusEnergy s-c)*z.q s)) := by
  let R : ℝ → ℝ := fun s => z.radiusEnergy s-c
  let G : ℝ → ℝ := fun s => z.rotationStress s +
    a * (z.p s*R s + h*(R s)^2/2)
  let W : ℝ → ℝ := fun s => (z.k s-h)*(R s*z.q s)
  have dR (s : ℝ) : HasDerivAt R (z.q s) s := (z.radiusEnergy_hasDerivAt s).sub_const c
  have cR : Continuous R := continuous_iff_continuousAt.mpr fun s => (dR s).continuousAt
  have cW : Continuous W := (z.continuous_k.sub continuous_const).mul (cR.mul z.continuous_q)
  have dG (s : ℝ) : HasDerivAt G (-b*(z.q s)^2 - a*W s) s := by
    convert (z.rotationStress_hasDerivAt s).add
      ((((z.dp s).mul (dR s)).add ((((dR s).pow 2).const_mul h).div_const 2)).const_mul a) using 1 <;>
      first | rfl | dsimp [force, W]; ring
  have ge : G L = G 0 := by
    dsimp [G, R, rotationStress, radiusEnergy]
    simp only [show z.p L=z.p 0 by simpa using z.periodic_p 0,
      show z.q L=z.q 0 by simpa using z.periodic_q 0,
      show z.k L=z.k 0 by simpa using z.periodic_k 0,
      show z.v L=z.v 0 by simpa using z.periodic_v 0]
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := L)
    (fun s _ => dG s)
    ((((z.continuous_q.pow 2).const_mul (-b)).sub (cW.const_mul a)).intervalIntegrable 0 L)
  rw [ge, sub_self, intervalIntegral.integral_sub
    (f := fun s => -b*(z.q s)^2) (g := fun s => a*W s)
    (((z.continuous_q.pow 2).const_mul (-b)).intervalIntegrable 0 L)
    ((cW.const_mul a).intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hI
  change (b/a)*(∫ s in 0..L, z.q s^2) = -(∫ s in 0..L, W s)
  field_simp [(z.dilation_pos hL).ne']
  linarith

private lemma mean_variance_identity {f : ℝ → ℝ} (hf : Continuous f) (hL : 0 < L) :
    L * (∫ s in 0..L, (f s-(∫ t in 0..L, f t)/L)^2) =
      L*(∫ s in 0..L, f s^2) - (∫ t in 0..L, f t)^2 := by
  let H := ∫ t in 0..L, f t
  let h := H/L
  have he : (fun s => (f s-h)^2) = (fun s => f s^2 - (2*h)*f s + h^2) := by
    funext s; ring
  change L*(∫ s in 0..L, (f s-h)^2) = L*(∫ s in 0..L, f s^2)-H^2
  rw [he, intervalIntegral.integral_add
    (f := fun s => f s^2-(2*h)*f s) (g := fun _ : ℝ => h^2)
    (((hf.pow 2).sub (hf.const_mul _)).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable 0 L),
    intervalIntegral.integral_sub (f := fun s => f s^2) (g := fun s => (2*h)*f s)
    ((hf.pow 2).intervalIntegrable 0 L) ((hf.const_mul _).intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  dsimp only [h,H]
  field_simp [hL.ne']
  ring

/-- The ratio b/a is bounded by the curvature oscillation on every genuine
nonconstant periodic support orbit, for any choice of the curvature center. -/
theorem rotation_pitch_sq_lt (hL : 0 < L) (hn : ¬∃ d, ∀ s, z.k s = d) (h : ℝ) :
    16 * (b/a)^2 < L * (∫ s in 0..L, (z.k s-h)^2) := by
  let Q := ∫ s in 0..L, z.q s^2
  let V := ∫ s in 0..L, |z.q s|
  let B := ∫ s in 0..L, (z.k s-h)^2
  have hQ : 0 < Q := z.tangent_support_square_pos hL hn
  have hV : 0 ≤ V :=
    intervalIntegral.integral_nonneg_of_forall hL.le (fun _ => abs_nonneg _)
  have hB : 0 < B := by
    by_contra! hh
    have h0 := le_antisymm hh
      (intervalIntegral.integral_nonneg_of_forall hL.le (fun s => sq_nonneg (z.k s-h)))
    have hpt := continuous_nonneg_zero_of_integral_zero hL
      ((z.continuous_k.sub continuous_const).pow 2) (fun s _ => sq_nonneg _) h0
    apply hn
    refine ⟨h, fun s => ?_⟩
    obtain ⟨t, ht, he⟩ := z.periodic_k.exists_mem_Ico₀ hL s
    exact he.trans (sub_eq_zero.mp (sq_eq_zero_iff.mp (hpt t ⟨ht.1, ht.2.le⟩)))
  have hV2 : V^2 < L*Q := by
    have hh := interval_integral_cauchy_sq (continuous_const (y := (1:ℝ)))
      z.continuous_q.abs hL.le
    have hweak : V^2 ≤ L*Q := by simpa [V,Q] using hh
    by_contra! hback
    have hv := mean_variance_identity z.continuous_q.abs hL
    simp only [sq_abs] at hv
    change L*(∫ s in 0..L, (|z.q s|-V/L)^2) = L*Q-V^2 at hv
    have hz : (∫ s in 0..L, (|z.q s|-V/L)^2) = 0 := by
      apply (mul_eq_zero.mp (show L*(∫ s in 0..L, (|z.q s|-V/L)^2) = 0
        by linarith)).resolve_left hL.ne'
    have hzpt := continuous_nonneg_zero_of_integral_zero hL
      ((z.continuous_q.abs.sub continuous_const).pow 2) (fun s _ => sq_nonneg _) hz
    have rc : Continuous z.radiusEnergy :=
      continuous_iff_continuousAt.mpr fun s => (z.radiusEnergy_hasDerivAt s).continuousAt
    obtain ⟨u, hu, hqu⟩ := exists_hasDerivAt_eq_zero hL rc.continuousOn
      (show z.radiusEnergy 0 = z.radiusEnergy L by simpa using (z.radiusEnergy_periodic 0).symm)
      (fun s _ => z.radiusEnergy_hasDerivAt s)
    have hzero := sq_eq_zero_iff.mp (hzpt u ⟨hu.1.le, hu.2.le⟩)
    change |z.q u|-V/L=0 at hzero
    rw [hqu, abs_zero, zero_sub, neg_eq_zero, div_eq_zero_iff] at hzero
    have hV0 := hzero.resolve_right hL.ne'
    rw [hV0, zero_pow (by decide), ← not_lt] at hback
    exact hback (mul_pos hL hQ)
  obtain ⟨c,hc⟩ := centered_primitive_bound hL z.radiusEnergy_hasDerivAt z.continuous_q
    (by simpa using z.radiusEnergy_periodic 0)
  let W : ℝ → ℝ := fun s => (z.radiusEnergy s-c)*z.q s
  have cR : Continuous z.radiusEnergy :=
    continuous_iff_continuousAt.mpr fun s => (z.radiusEnergy_hasDerivAt s).continuousAt
  have cW : Continuous W := (cR.sub continuous_const).mul z.continuous_q
  have hW : (∫ s in 0..L, W s ^ 2) ≤ (V/4)^2 * Q := by
    rw [show (V/4)^2*Q = (∫ s in 0..L, (V/4)^2*(z.q s)^2) by
      rw [intervalIntegral.integral_const_mul]]
    apply intervalIntegral.integral_mono_on hL.le ((cW.pow 2).intervalIntegrable _ _)
      (((z.continuous_q.pow 2).const_mul _).intervalIntegrable _ _)
    intro s hs
    have hh : (z.radiusEnergy s-c)^2 ≤ (V/4)^2 := by
      have hm := hc s hs
      change |z.radiusEnergy s-c| ≤ V/4 at hm
      simpa only [sq_abs] using (sq_le_sq' (by linarith [abs_nonneg (z.radiusEnergy s-c)]) hm)
    change ((z.radiusEnergy s-c)*z.q s)^2 ≤ (V/4)^2*(z.q s)^2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  have cs := interval_integral_cauchy_sq (z.continuous_k.sub (continuous_const (y := h)))
    cW hL.le
  have hid := z.centered_pitch_identity hL c h
  change (b/a)*Q = -(∫ s in 0..L, (z.k s-h)*W s) at hid
  have ih : (∫ s in 0..L, (z.k s-h)*W s) = -((b/a)*Q) := by linarith
  change (∫ s in 0..L, (z.k s-h)*W s)^2 ≤ B*(∫ s in 0..L, W s^2) at cs
  rw [ih, neg_sq] at cs
  have h1 := cs.trans (mul_le_mul_of_nonneg_left hW hB.le)
  have h2 := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hV2 hB) hQ
  change 16 * (b/a)^2 < L*B
  apply lt_of_mul_lt_mul_right (a := Q^2) _ (sq_nonneg Q)
  nlinarith only [h1, h2]

/-- Taking the mean curvature gives the rotation bound in variance form. -/
theorem rotation_pitch_curvature_variance (hL : 0 < L) (hn : ¬∃ d, ∀ s, z.k s = d) :
    16 * (b/a)^2 ≤ L * (∫ s in 0..L, (z.k s - (∫ t in 0..L, z.k t)/L)^2) :=
  (z.rotation_pitch_sq_lt hL hn _).le

/-- A full closed period with turning number m costs more than the sum of
the quadratic turning and rotation terms in the length-energy product. -/
theorem turning_pitch_energy_lt (hL : 0 < L) (hn : ¬∃ d, ∀ s, z.k s = d)
    (m : ℤ) (hturn : (∫ s in 0..L, z.k s) = (2*Real.pi)*m) :
    2 * Real.pi^2*(m:ℝ)^2 + 8*(b/a)^2 < L*(z.bending/2) := by
  have hh := z.rotation_pitch_sq_lt hL hn ((∫ s in 0..L, z.k s)/L)
  rw [mean_variance_identity z.continuous_k hL, hturn] at hh
  dsimp only [bending]
  nlinarith only [hh]

end PeriodicSupportProfile
end ClosedSimilarity

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Rotation-pitch audit failed for {name} at {axiomName}"
      count := count + 1
  logInfo m!"Rotation-pitch audit passed for {count} declarations."
