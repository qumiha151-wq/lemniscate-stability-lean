import LengthGrowth.ActualFlow.RecordCurvature

/-! A criterion using elapsed physical time on the given flow. -/

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

def normalizedDissipation (t : ℝ) := c.dissipation t / c.energy t ^ 5

theorem normalizedDissipation_continuousOn :
    ContinuousOn c.normalizedDissipation (Ici 0) :=
  c.dissipation_continuousOn.div (c.energy_continuousOn.pow 5)
    (fun _ ht => pow_ne_zero _ (c.energy_pos ht).ne')

theorem inverse_fourth_physical_time (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (c.energy t)⁻¹ ^ 4 = (c.energy s)⁻¹ ^ 4 + 4 * ∫ x in s..t, c.normalizedDissipation x := by
  have sub : Icc s t ⊆ Ici 0 := fun _ hy => hs.trans hy.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (((c.energy_continuousOn.inv₀ (fun _ hy => (c.energy_pos hy).ne')).pow 4).mono sub)
    (fun x hx => FreeElasticScalar.inverse_fourth_hasDerivAt (c.energy_pos (hs.trans hx.1.le)).ne'
      (c.energy_hasDerivAt_normal hflow (hs.trans_lt hx.1)))
    (((c.normalizedDissipation_continuousOn.mono sub).const_mul 4).intervalIntegrable_of_Icc hst)
  change (∫ x in s..t, 4 * c.normalizedDissipation x) = (c.energy t)⁻¹ ^ 4 - (c.energy s)⁻¹ ^ 4 at h
  rw [intervalIntegral.integral_const_mul] at h
  linarith

/-- Failure of quarter growth forces arbitrarily small physical-time average
of D/E⁵ over arbitrarily late horizons measured from the initial curve. -/
theorem exists_small_average_of_not_quarter (hflow : c.IsNormalFEF)
    (hnot : ¬ c.HasQuarterLengthBound) {ε : ℝ} (hε : 0 < ε) (S : ℝ) :
    ∃ t, max S 1 < t ∧ (∫ x in 0..t, c.normalizedDissipation x) < ε * t := by
  let s := max S 1
  have hs : 1 ≤ s := le_max_right _ _
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  let q := FreeElasticScalar.fourthRoot
  let b := max (c.energy 0 * q (1+s)) (q (1/ε))
  have hpos := FreeElasticScalar.fourthRoot_pos (one_div_pos.mpr hε)
  have hb : 0 < b := hpos.trans_le (le_max_right _ _)
  have hen : ¬ c.HasQuarterEnergyBound := fun h => hnot (c.quarter_length_of_quarter_energy hflow h)
  have bad : ∃ t, 0 ≤ t ∧ b / q (1+t) < c.energy t := by
    by_contra! no
    exact hen ⟨b,hb,no⟩
  obtain ⟨t, ht, he⟩ := bad
  have hqt : 0 < q (1+t) := FreeElasticScalar.fourthRoot_pos (by linarith)
  have high := (div_lt_iff₀ hqt).mp he
  have hst : s < t := by
    by_contra! hh
    have hbound := mul_le_mul
      (c.energy_le_of_le hflow (s := 0) le_rfl ht)
      (FreeElasticScalar.fourthRoot_mono (show 1 + t ≤ 1 + s by linarith))
      hqt.le (c.energy_nonneg 0)
    exact high.not_ge (hbound.trans (le_max_left _ _))
  have he4 := pow_lt_pow_left₀ high hb.le (by norm_num : (4 : ℕ) ≠ 0)
  dsimp only [q] at he4
  rw [mul_pow, FreeElasticScalar.fourthRoot_pow_four (show 0 ≤ 1+t by linarith)] at he4
  have hb4 := pow_le_pow_left₀ hpos.le (show q (1/ε) ≤ b from le_max_right _ _) 4
  rw [FreeElasticScalar.fourthRoot_pow_four (one_div_pos.mpr hε).le] at hb4
  have hE := c.energy_pos ht
  have invbound : (c.energy t)⁻¹ ^ 4 < ε * (1+t) := by
    rw [inv_pow, ← one_div]
    apply (div_lt_iff₀ (pow_pos hE 4)).mpr
    have hi := (div_lt_iff₀ hε).mp (hb4.trans_lt he4)
    linarith only [show (c.energy t ^ 4 * (1+t)) * ε = ε * (1+t) * c.energy t ^ 4 by ring, hi]
  have eqn := c.inverse_fourth_physical_time hflow (s := 0) le_rfl ht
  have hdiff := mul_le_mul_of_nonneg_left (hs.trans hst.le) hε.le
  refine ⟨t,hst,?_⟩
  nlinarith only [eqn, invbound, hdiff, pow_nonneg (inv_nonneg.mpr (c.energy_nonneg 0)) 4,
    mul_nonneg hε.le ht, hε]

/-- Every continuous time weight supported where the product is at most K
has small occupation integral on the same horizon. The horizon is chosen
before the weight. -/
theorem exists_small_bounded_product_occupation (hflow : c.IsNormalFEF)
    (hnot : ¬ c.HasQuarterLengthBound) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (S : ℝ) :
    ∃ t, max S 1 < t ∧ ∀ w : ℝ → ℝ, ContinuousOn w (Icc 0 t) →
      (∀ x ∈ Icc 0 t, w x ≤ 1) →
      (∀ x ∈ Icc 0 t, K < c.normalizedProduct x → w x = 0) →
      (∫ x in 0..t, w x) < ε * t := by
  let C := 2097152 * K ^ 3
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨t, ht, hmean⟩ := c.exists_small_average_of_not_quarter hflow hnot (div_pos hε hC) S
  have ht0 : 0 ≤ t := ((le_max_right S 1).trans ht.le).trans' zero_le_one
  refine ⟨t, ht, ?_⟩
  intro w hw hcap hsupp
  have bound (x : ℝ) (hx : x ∈ Icc 0 t) : w x ≤ C * c.normalizedDissipation x := by
    have hp := c.energy_pos hx.1
    have hl := c.length_pos hx.1
    have hdn : 0 ≤ c.normalizedDissipation x :=
      div_nonneg (c.dissipation_nonneg _) (pow_nonneg hp.le _)
    by_cases h : K < c.normalizedProduct x
    · rw [hsupp x hx h]
      exact mul_nonneg hC.le hdn
    · have hprod := pow_le_pow_left₀ (c.normalizedProduct_nonneg x) (le_of_not_gt h) 3
      have hvir := (div_le_iff₀ (pow_pos hl 3)).mp (c.weak_virial hx.1)
      have hscale := mul_le_mul_of_nonneg_right hvir (pow_nonneg hp.le 3)
      have hcost := mul_le_mul_of_nonneg_left hprod (c.dissipation_nonneg x)
      dsimp [normalizedProduct] at hcost
      apply (hcap x hx).trans
      change 1 ≤ C * (c.dissipation x / c.energy x ^ 5)
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (pow_pos hp 5)).mpr
      dsimp [C]
      nlinarith only [hcost,hscale]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht0 (hw.intervalIntegrable_of_Icc ht0)
    (((c.normalizedDissipation_continuousOn.mono (show Icc 0 t ⊆ Ici 0 from fun _ hx => hx.1)).const_mul C).intervalIntegrable_of_Icc ht0) bound
  rw [intervalIntegral.integral_const_mul] at hmono
  apply lt_of_le_of_lt hmono
  calc
    _ < C * (ε / C * t) := mul_lt_mul_of_pos_left hmean hC
    _ = ε * t := by field_simp [hC.ne']

end LengthGrowth.ActualFlow.ForwardImmersion
