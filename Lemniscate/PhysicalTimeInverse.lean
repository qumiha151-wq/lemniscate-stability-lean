import Lemniscate.PhysicalNormalization

/-! The exact inverse clock permits a given physical curve flow to be
compared with the constructed solution in normalized time. -/
noncomputable section
namespace Lemniscate

def physicalTime (a σ : ℝ) : ℝ := a^4*(Real.exp (30*σ)-1)/30

/-- The normalized and physical clocks are actual inverses on their
nonnegative axes; their displayed derivatives are the true derivatives. -/
theorem physical_time_inverse (a : ℝ) (ha : 0<a) :
    physicalTime a 0=0 ∧
      (∀ σ : ℝ, normalizedTime a (physicalTime a σ)=σ ∧
        HasDerivAt (physicalTime a) (a^4+30*physicalTime a σ) σ ∧
        (0≤σ → 0≤physicalTime a σ) ∧ (0<σ → 0<physicalTime a σ)) ∧
      ∀ t : ℝ, 0≤t → physicalTime a (normalizedTime a t)=t := by
  have ha₄ : a^4≠0 := pow_ne_zero 4 ha.ne'
  have hbase (σ : ℝ) : timeBase a (physicalTime a σ)=Real.exp (30*σ) := by
    dsimp only [timeBase,physicalTime]
    field_simp [ha₄]
    <;> ring
  refine ⟨by simp [physicalTime],?_,?_⟩
  · intro σ
    have hclock : normalizedTime a (physicalTime a σ)=σ := by
      dsimp only [normalizedTime]
      rw [hbase,Real.log_exp]
      ring
    have hd := (((hasDerivAt_id σ).const_mul 30).exp.sub_const 1).const_mul (a^4)
    have hd' : HasDerivAt (physicalTime a) (a^4+30*physicalTime a σ) σ := by
      convert! hd.div_const 30 using 1
      dsimp only [physicalTime,id_eq]
      ring
    refine ⟨hclock,hd',?_,?_⟩
    · intro hσ
      have he : 1≤Real.exp (30*σ) := Real.one_le_exp_iff.mpr (by linarith)
      exact div_nonneg (mul_nonneg (pow_nonneg ha.le 4) (sub_nonneg.mpr he)) (by norm_num)
    · intro hσ
      have he : 1<Real.exp (30*σ) := Real.one_lt_exp_iff.mpr (by linarith)
      exact div_pos (mul_pos (pow_pos ha 4) (sub_pos.mpr he)) (by norm_num)
  · intro t ht
    have he : Real.exp (30*normalizedTime a t)=timeBase a t := by
      have harg : 30*normalizedTime a t=Real.log (timeBase a t) := by
        dsimp only [normalizedTime]
        ring
      rw [harg,Real.exp_log (timeBase_pos a t ha ht)]
    dsimp only [physicalTime]
    rw [he]
    dsimp only [timeBase]
    field_simp [ha₄]
    <;> ring

end Lemniscate
