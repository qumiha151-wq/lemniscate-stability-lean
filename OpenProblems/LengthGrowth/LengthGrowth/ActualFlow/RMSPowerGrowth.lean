import LengthGrowth.ActualFlow.RMSTypeI

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The positive root of a²=r²(1−2a) yields a strictly sub-square-root exponent. -/
def rmsPower (r : ℝ) : ℝ := r*Real.sqrt (1+r^2)-r^2

theorem rmsPower_spec {r : ℝ} (hr : 0<r) :
    0<rmsPower r ∧ rmsPower r<1/2 ∧ (rmsPower r)^2=r^2*(1-2*rmsPower r) := by
  have hs:=Real.sq_sqrt (show 0≤1+r^2 by positivity)
  have gt : r<Real.sqrt (1+r^2) := by
    by_contra! h
    nlinarith only [hs,mul_self_le_mul_self (Real.sqrt_nonneg _) h]
  have pos : 0<rmsPower r := by
    dsimp [rmsPower]
    nlinarith only [mul_pos hr (sub_pos.mpr gt)]
  have eq : (rmsPower r)^2=r^2*(1-2*rmsPower r) := by
    dsimp [rmsPower]
    nlinarith only [congrArg (fun z : ℝ => r^2*z) hs]
  have small : rmsPower r<1/2 := by
    by_contra! bad
    nlinarith only [eq,sq_pos_of_pos pos,mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r)
      (show 1-2*rmsPower r≤0 by linarith)]
  exact ⟨pos,small,eq⟩

private theorem length_power_of_weighted (hf : c.IsNormalFEF) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (cap : ∀t≥T,(1-2*a)*(t*c.energy t^2)≤a^2*c.length t^2) :
    ∃K : ℝ, 0<K ∧ ∀t≥T,c.length t ≤ K*t^a := by
  let B:=c.rmsWeighted a T*T^(-2*a)
  have bp : 0<B := by
    have el:=c.length_pos hT.le
    dsimp [B,rmsWeighted]
    positivity
  refine ⟨1+B/a,by positivity,?_⟩
  intro t ht
  have tp:=hT.trans_le ht
  have bound:=c.rms_weighted_antitone hf hT cap (mem_Ici.mpr (le_refl T)) (mem_Ici.mpr ht) ht
  have sq : a*(c.length t*t^(-a))^2 ≤ B := by
    calc
      _ = a*c.length t^2*t^(-2*a) := by
        rw [mul_pow,←Real.rpow_natCast (t^(-a)) 2,←Real.rpow_mul tp.le]
        norm_num
        ring_nf
      _ ≤ _ := by
        apply le_trans _ bound
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg tp.le _)
        dsimp [rmsWeighted]
        exact le_add_of_nonneg_right (mul_nonneg tp.le (sq_nonneg _))
  have q : (c.length t*t^(-a))^2 ≤ B/a := by
    apply (le_div_iff₀ ha).mpr
    linarith only [sq]
  have linear : c.length t*t^(-a) ≤ 1+B/a := by
    nlinarith only [q,sq_nonneg (c.length t*t^(-a)-1/2)]
  rw [Real.rpow_neg tp.le,←div_eq_mul_inv] at linear
  exact (div_le_iff₀ (Real.rpow_pos_of_pos tp _)).mp linear

/-- RMS Type I bounds the actual length and bending energy by complementary powers. -/
theorem rms_typeI_power_rates (hf : c.IsNormalFEF) {T r : ℝ} (hT : 0<T) (hr : 0<r)
    (cap : ∀t≥T,Real.sqrt t*c.energy t ≤ r*c.length t) :
    ∃K : ℝ, 0<K ∧ ∀t≥T, c.length t≤K*t^(rmsPower r) ∧
      c.energy t≤(r*K)*t^(rmsPower r-1/2) := by
  obtain ⟨pos,small,eq⟩:=rmsPower_spec hr
  have h (t : ℝ) (ht : T≤t) : t*c.energy t^2≤r^2*c.length t^2 := by
    have e:=c.energy_pos (hT.trans_le ht).le
    have hsq:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) e.le) (cap t ht) 2
    rwa [mul_pow,mul_pow,Real.sq_sqrt (hT.trans_le ht).le] at hsq
  obtain ⟨K,kp,len⟩:=c.length_power_of_weighted hf pos hT (fun t ht => by
    rw [eq]
    nlinarith only [mul_le_mul_of_nonneg_left (h t ht)
      (show 0≤1-2*rmsPower r by linarith)])
  refine ⟨K,kp,fun t ht => ⟨len t ht,?_⟩⟩
  have tp:=hT.trans_le ht
  rw [Real.rpow_sub tp,←Real.sqrt_eq_rpow]
  rw [←mul_div_assoc,le_div_iff₀ (Real.sqrt_pos.mpr tp)]
  nlinarith only [cap t ht,mul_le_mul_of_nonneg_left (len t ht) hr.le]

/-- The critical RMS condition is sqrt(t) E/L ≤ 1/sqrt(8). -/
theorem quarter_length_of_critical_rms (hf : c.IsNormalFEF) {T : ℝ} (hT : 0<T)
    (cap : ∀t≥T,8*t*c.energy t^2≤c.length t^2) : c.HasQuarterLengthBound := by
  obtain ⟨K,kp,len⟩ := c.length_power_of_weighted hf (by norm_num : (0:ℝ)<1/4) hT
    (fun t ht => by nlinarith only [cap t ht])
  obtain ⟨s,hs,mx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT.le)
    (c.length_continuousOn.mono (show Icc 0 T⊆Ici 0 from fun _ hx => hx.1))
  refine ⟨max K (c.length s),lt_of_lt_of_le kp (le_max_left ..),?_⟩
  intro t ht
  have pow : FreeElasticScalar.fourthRoot (1+t)=(1+t)^(1/4:ℝ) := by
    rw [FreeElasticScalar.fourthRoot,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
      ←Real.rpow_mul (by linarith : 0≤1+t)]
    norm_num
  rw [pow]
  by_cases early : t≤T
  · have m:=mx (show t∈Icc 0 T from ⟨ht,early⟩)
    exact le_trans (le_trans m (le_max_right ..)) (le_mul_of_one_le_right
      (le_of_lt (lt_of_lt_of_le kp (le_max_left ..)))
      (Real.one_le_rpow (by linarith) (by norm_num)))
  · exact (len t (le_of_not_ge early)).trans (mul_le_mul (le_max_left ..)
      (Real.rpow_le_rpow ht (by linarith) (by norm_num)) (Real.rpow_nonneg ht _)
      (le_of_lt (lt_of_lt_of_le kp (le_max_left ..))))

theorem quarter_length_of_rms_sqrt_eight (hf : c.IsNormalFEF) {T : ℝ} (hT : 0<T)
    (cap : ∀t≥T,Real.sqrt t*c.energy t≤c.length t/Real.sqrt 8) :
    c.HasQuarterLengthBound := by
  apply c.quarter_length_of_critical_rms hf hT
  intro t ht
  have tp:=hT.trans_le ht
  have hs:=(le_div_iff₀ (by positivity : 0<Real.sqrt 8)).mp (cap t ht)
  have e:=c.energy_nonneg t
  have sq:=pow_le_pow_left₀ (by positivity : 0≤Real.sqrt t*c.energy t*Real.sqrt 8) hs 2
  rw [mul_pow,mul_pow,Real.sq_sqrt tp.le,Real.sq_sqrt (by norm_num : (0:ℝ)≤8)] at sq
  linarith only [sq]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.rms_typeI_power_rates
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_critical_rms
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_rms_sqrt_eight
