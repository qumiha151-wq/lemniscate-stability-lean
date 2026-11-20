import SolitonClassification.OuterStress
import SolitonClassification.FrozenStressTail

/-! Finite-time estimates descending from fixed stress to the transition layer. -/
noncomputable section
open Set
namespace ClosedSimilarity.OuterStress

/-- Integrate the transverse error against the *corrected* decreasing
    amplitude. The actual amplitude may have arbitrarily many critical points. -/
theorem descending_impact {S T c B : ℝ} {H J A : ℝ → ℝ}
    (st : S ≤ T) (hc : 0 < c) (hB : 0 ≤ B)
    (hH : ContinuousOn H (Icc S T)) (hJ : ContinuousOn J (Icc S T))
    (hp : ∀ x ∈ Icc S T, 0 < H x)
    (rate : ∀ x ∈ Ioo S T, DifferentiableAt ℝ H x ∧ DifferentiableAt ℝ J x ∧
      deriv H x ≤ -c ∧ |deriv J x| ≤ B/(A x)^2 ∧ H x ≤ 2*A x) :
    |J T-J S| ≤ 4*B/(c*H T) := by
  let v := fun x : ℝ => H (-x)/2
  let j := fun x : ℝ => J (-x)
  have m : MapsTo (fun x : ℝ => -x) (Icc (-T) (-S)) (Icc S T) := by
    intro x hx; exact ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hneg : Continuous (fun x : ℝ => -x) := continuous_neg
  have vv : ContinuousOn v (Icc (-T) (-S)) := (hH.comp hneg.continuousOn m).div_const 2
  have jj : ContinuousOn j (Icc (-T) (-S)) := hJ.comp hneg.continuousOn m
  have out := FrozenStress.corrected_tail (A := fun x => A (-x)) (d := 0) (c := c/2)
    (neg_le_neg st) hB (by positivity) vv jj
    (fun x hx => by dsimp [v]; linarith [hp _ (m hx)])
    (fun x hx => by
      have inside : -x ∈ Ioo S T := ⟨by linarith [hx.2],by linarith [hx.1]⟩
      obtain ⟨h₁,h₂,dh,dj,ha⟩ := rate _ inside
      have dv : HasDerivAt v (-deriv H (-x)/2) x := by
        convert! (h₁.hasDerivAt.comp x (hasDerivAt_id x).neg).div_const 2 using 1
        ring
      have dJ : HasDerivAt j (-deriv J (-x)) x := by
        convert! h₂.hasDerivAt.comp x (hasDerivAt_id x).neg using 1
        ring
      refine ⟨dv.differentiableAt,dJ.differentiableAt,?_,?_,?_⟩
      · rw [dv.deriv]; linarith
      · rwa [dJ.deriv,abs_neg]
      · dsimp [v]; linarith)
  simp only [v,j,neg_neg,sub_zero] at out
  rw [abs_sub_comm]
  convert out using 1
  ring

/-- Integrable O(δ/A²) drift up to the final instant of an actual outer
    trajectory satisfying the corrected-amplitude descent and size bounds. -/
theorem impact_on_descent (M : ℝ) : ∃ C ≥ 0, ∀ {S T δ c : ℝ} {r U w a b : ℝ → ℝ},
    S ≤ T → 0 < c →
    (∀ x ∈ Icc S T, Rates δ x r U w a b ∧ r x^2 ≤ 1 ∧ |a x| ≤ M ∧ |b x| ≤ M ∧
      0 < amplitude δ r U w a b x ∧ amplitude δ r U w a b x ≤ 2*r x^2) →
    (∀ x ∈ Ioo S T, deriv (amplitude δ r U w a b) x ≤ -c) →
    |impact δ r U w a b T - impact δ r U w a b S| ≤
      4*C*δ/(c*amplitude δ r U w a b T) := by
  obtain ⟨C,hC,un⟩ := uniform_rates M
  refine ⟨C,hC,?_⟩
  intro S T δ c r U w a b st hc data speed
  have dp := (data S ⟨le_rfl,st⟩).1.delta_pos
  have e := descending_impact (A := fun x => r x^2) st hc (mul_nonneg hC dp.le)
    (fun x hx => (amplitude_rate (data x hx).1).continuousAt.continuousWithinAt)
    (fun x hx => (impact_rate (data x hx).1).continuousAt.continuousWithinAt)
    (fun x hx => (data x hx).2.2.2.2.1)
    (fun x hx => by
      obtain ⟨d,hr,ha,hb,_,bound⟩ := data x ⟨hx.1.le,hx.2.le⟩
      refine ⟨(amplitude_rate d).differentiableAt,(impact_rate d).differentiableAt,speed x hx,?_,bound⟩
      convert (un d hr ha hb).1 using 1; ring)
  simpa only [mul_assoc] using e

private theorem q_bound {u w a b M : ℝ} (osc : (u^2/2)^2+w^2=1)
    (ha : |a| ≤ M) (hb : |b| ≤ M) : |Q u w a b| ≤ 3*M := by
  have m := (abs_nonneg a).trans ha
  have usq : u^2 ≤ 2 := by nlinarith [sq_nonneg w,sq_nonneg (u^2/2-1)]
  have hu : |u| ≤ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg (u+1)],by nlinarith [sq_nonneg (u-1)]⟩
  have hw : |w| ≤ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg (u^2/2),sq_nonneg (w+1)],
    by nlinarith [sq_nonneg (u^2/2),sq_nonneg (w-1)]⟩
  calc
    |Q u w a b| ≤ |-(u*w*a/3)|+|u^3*b/6| := by
      unfold Q
      simpa only [sub_eq_add_neg,abs_neg,neg_mul,neg_div] using abs_add_le (-u*w*a/3) (-(u^3*b/6))
    _ = |u| * |w| * |a| /3+ |u| ^3 * |b| /6 := by
      simp [abs_mul,abs_div,abs_pow]
    _ ≤ (2*2*M)/3+(2^3*M)/6 := by gcongr
    _ ≤ 3*M := by linarith

/-- Above the critical scale r³ ≥ Lδ, a positive radial component alone
    ensures descent. All constants are independent of the final amplitude. -/
theorem descent_threshold (M α : ℝ) (hα : 0 < α) : ∃ L > 0,
    ∀ {δ s : ℝ} {r U w a b : ℝ → ℝ}, Rates δ s r U w a b →
    r s^2 ≤ 1 → |a s| ≤ M → |b s| ≤ M → α ≤ a s → L*δ ≤ r s^3 →
    r s^2/2 ≤ amplitude δ r U w a b s ∧ amplitude δ r U w a b s ≤ 2*r s^2 ∧
    deriv (amplitude δ r U w a b) s ≤ -α/3 := by
  obtain ⟨C,hC,un⟩ := uniform_rates M
  let L := max 1 (max (6*M) (3*C/α))
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨L,hL,?_⟩
  intro δ s r U w a b d hr ha hb hal large
  have m : 6*M ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have c : 3*C/α ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have h₁ := (mul_le_mul_of_nonneg_right m d.delta_pos.le).trans large
  have h₂ := (div_le_iff₀ hα).mp c
  have h₃ := mul_le_mul_of_nonneg_right h₂ d.delta_pos.le
  have h₄ := mul_le_mul_of_nonneg_left large hα.le
  have ac : C*δ/r s^3 ≤ α/3 := (div_le_iff₀ (pow_pos d.pos 3)).mpr (by nlinarith)
  have rate := ((abs_le.mp (un d hr ha hb).2).2).trans ac
  have q := abs_le.mp (q_bound d.oscillator ha hb)
  have minus := mul_le_mul_of_nonneg_left q.1 d.delta_pos.le
  have plus := mul_le_mul_of_nonneg_left q.2 d.delta_pos.le
  have mag : δ*(Q (U s) (w s) (a s) (b s)/r s) ≤ r s^2/2 ∧
      -(r s^2/2) ≤ δ*(Q (U s) (w s) (a s) (b s)/r s) := by
    rw [←mul_div_assoc]
    exact ⟨(div_le_iff₀ d.pos).mpr (by nlinarith),(le_div_iff₀ d.pos).mpr (by nlinarith)⟩
  exact ⟨by dsimp [amplitude]; linarith [mag.1],
    by dsimp [amplitude]; linarith [mag.2,sq_nonneg (r s)],by linarith⟩

theorem transverse_error_above_layer (M α : ℝ) (hα : 0 < α) : ∃ L > 0, ∃ C ≥ 0,
    ∀ {S T δ : ℝ} {r U w a b : ℝ → ℝ}, S ≤ T →
    (∀ x ∈ Icc S T, Rates δ x r U w a b ∧ r x^2 ≤ 1 ∧ |a x| ≤ M ∧ |b x| ≤ M ∧
      α ≤ a x ∧ L*δ ≤ r x^3) →
    |impact δ r U w a b T - impact δ r U w a b S| ≤ C*δ/r T^2 := by
  obtain ⟨L,hL,h⟩ := descent_threshold M α hα
  obtain ⟨C,hC,budget⟩ := impact_on_descent M
  refine ⟨L,hL,24*C/α,by positivity,?_⟩
  intro S T δ r U w a b st data
  let H := amplitude δ r U w a b
  have estimates (x : ℝ) (hx : x ∈ Icc S T) :=
    let ⟨d,small,ha,hb,align,above⟩ := data x hx
    h d small ha hb align above
  have pos (x : ℝ) (hx : x ∈ Icc S T) : 0 < H x :=
    lt_of_lt_of_le (by have := (data x hx).1.pos; positivity) (estimates x hx).1
  have e := budget st (show (0:ℝ)<α/3 by positivity)
    (fun x hx => ⟨(data x hx).1,(data x hx).2.1,(data x hx).2.2.1,(data x hx).2.2.2.1,
      pos x hx,(estimates x hx).2.1⟩)
    (fun x hx => by simpa only [neg_div] using (estimates x ⟨hx.1.le,hx.2.le⟩).2.2)
  apply e.trans
  have ht : T ∈ Icc S T := ⟨st,le_rfl⟩
  have rt := (data T ht).1.pos
  have dp := (data T ht).1.delta_pos
  have denom : α/3*(r T^2/2) ≤ α/3*H T :=
    mul_le_mul_of_nonneg_left (estimates T ht).1 (by positivity)
  calc
    _ ≤ (4*C*δ)/(α/3*(r T^2/2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) denom
    _ = _ := by ring

end ClosedSimilarity.OuterStress
#print axioms ClosedSimilarity.OuterStress.impact_on_descent
#print axioms ClosedSimilarity.OuterStress.transverse_error_above_layer
