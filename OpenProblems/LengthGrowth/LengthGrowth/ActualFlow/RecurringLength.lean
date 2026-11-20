import LengthGrowth.ActualFlow.GrowthEnvelope

noncomputable section
open Set

namespace LengthGrowth.ActualFlow

/-- If elapsed physical time scales by the fourth power of the recurrent
length factor, the length to the fourth power is comparable to elapsed
time on the whole tail. Continuity and positivity are only needed there. -/
theorem recurring_length_fourth_power_bounds (L : ℝ → ℝ) {r u₀ : ℝ}
    (hr : 1 < r) (h₀ : 0 < u₀) (hc : ContinuousOn L (Ici u₀))
    (hp : ∀ u, u₀ ≤ u → 0 < L u)
    (hs : ∀ u, u₀ ≤ u → L (r ^ 4 * u) = r * L u) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ u, u₀ ≤ u → c * u ≤ L u ^ 4 ∧ L u ^ 4 ≤ C * u := by
  let a := r ^ 4
  have ha : 1 < a := one_lt_pow₀ hr (by decide : 4 ≠ 0)
  have ha0 : 0 < a := zero_lt_one.trans ha
  let f := fun u : ℝ => L u ^ 4 / u
  let I := Icc u₀ (a * u₀)
  have hI : I.Nonempty := ⟨u₀, le_rfl, le_mul_of_one_le_left h₀.le ha.le⟩
  have hfc : ContinuousOn f I :=
    ((hc.mono fun _ hx => hx.1).pow 4).div continuousOn_id
      (fun _ hx => (h₀.trans_le hx.1).ne')
  obtain ⟨p, hpi, hmin⟩ := isCompact_Icc.exists_isMinOn hI hfc
  obtain ⟨q, hqi, hmax⟩ := isCompact_Icc.exists_isMaxOn hI hfc
  have fpos (v : ℝ) (hv : u₀ ≤ v) : 0 < f v :=
    div_pos (pow_pos (hp v hv) _) (h₀.trans_le hv)
  have step (v : ℝ) (hv : u₀ ≤ v) : f (a * v) = f v := by
    dsimp only [f, a]
    rw [hs v hv, mul_pow]
    field_simp [ne_of_gt (zero_lt_one.trans hr), (h₀.trans_le hv).ne']
  have iter (n : ℕ) (v : ℝ) (hv : u₀ ≤ v) : f (a ^ n * v) = f v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, step, ih]
      exact hv.trans (le_mul_of_one_le_left (h₀.trans_le hv).le (one_le_pow₀ ha.le))
  refine ⟨f p, f q, fpos p hpi.1, fpos q hqi.1, ?_⟩
  intro u hu
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_div h₀).2 hu) ha
  let v := u / a ^ n
  have han : 0 < a ^ n := pow_pos ha0 n
  have hlo : u₀ ≤ v :=
    (le_div_iff₀ han).2 (by simpa [mul_comm] using (le_div_iff₀ h₀).1 hn)
  have hhi : v ≤ a * u₀ := by
    apply (div_le_iff₀ han).2
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using ((div_lt_iff₀ h₀).1 hn').le
  have vi : v ∈ I := ⟨hlo, hhi⟩
  have fu : f u = f v := by
    convert iter n v hlo using 2
    dsimp [v]
    field_simp
  have hbounds : f p ≤ f u ∧ f u ≤ f q := fu ▸ ⟨hmin vi, hmax vi⟩
  exact ⟨(le_div_iff₀ (h₀.trans_le hu)).1 hbounds.1,
    (div_le_iff₀ (h₀.trans_le hu)).1 hbounds.2⟩

#print axioms recurring_length_fourth_power_bounds

end LengthGrowth.ActualFlow
