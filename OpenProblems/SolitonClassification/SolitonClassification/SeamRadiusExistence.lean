import SolitonClassification.PhysicalSeamScale

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set

/-- Prescribing a physical radius at a bounded continuous travel time along
    the true seam solutions. The same smallness condition works for every
    real seam curvature, including the two certified endpoint shots. -/
theorem exists_prescribed_seam_scale (c e T : ℝ) (he : 0 < e)
    (small : 4*e*T ≤ 1/2) (time : ℝ → ℝ)
    (hc : ContinuousOn time (Icc 0 (4*e)))
    (bounded : ∀ d ∈ Icc 0 (4*e), |time d| ≤ T) :
    ∃ d ∈ Ioc 0 (4*e), ∃ l > (0:ℝ), l^4*d = 1 ∧
      ReflectedArc.RadialLayer.eps (solution 1 (restore l ![c,0,1,0])) (time d/l) = e := by
  let x : Phase := ![c,0,1,0]
  let A := fun d : ℝ => radiusSq (solution d x (time d))
  let S := Icc (0:ℝ) (4*e)
  have endpos : 0 ≤ 4*e := by positivity
  have r (d : ℝ) (hd : d ∈ S) : 0 < A d ∧ A d ≤ 4 := by
    have b := radius_speed d x 0 (time d)
    have h0 : radiusSq (solution d x 0) = 1 := by simp [solution_zero,x,radiusSq]
    rw [h0,Real.sqrt_one,sub_zero,abs_of_nonneg hd.1] at b
    have ht := (mul_le_mul hd.2 (bounded d hd) (abs_nonneg _) endpos).trans small
    change |Real.sqrt (A d)-1| ≤ _ at b
    obtain ⟨lo,hi⟩ := abs_le.mp (b.trans ht)
    have s := Real.sq_sqrt (show 0 ≤ A d by unfold A radiusSq; positivity)
    constructor <;> nlinarith
  have cs : ContinuousOn A S := by
    have input : ContinuousOn (fun d : ℝ => ((time d,(d,x)) : ℝ × Data)) S :=
      hc.prodMk (continuousOn_id.prodMk continuousOn_const)
    have z := continuous_solution.continuousOn.comp input (mapsTo_univ _ _)
    have ev (i : Fin 4) := (continuous_apply i).continuousOn.comp z (mapsTo_univ _ _)
    exact ((ev 2).pow 2).add ((ev 3).pow 2)
  let F := fun d => d*(A d)^(-2/3:ℝ)
  have cf : ContinuousOn F S := continuousOn_id.mul
    (cs.rpow_const fun d hd => Or.inl (r d hd).1.ne')
  have hh : 4*e ∈ S := ⟨endpos,le_rfl⟩
  have powbound : (A (4*e))^(2/3:ℝ) ≤ 4 := by
    calc
      _ ≤ (4:ℝ)^(2/3:ℝ) := Real.rpow_le_rpow (r _ hh).1.le (r _ hh).2 (by norm_num)
      _ ≤ (4:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := Real.rpow_one _
  have last : e ≤ F (4*e) := by
    dsimp [F]
    rw [show (-2/3:ℝ)= -(2/3:ℝ) by ring,Real.rpow_neg (r _ hh).1.le,← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (r _ hh).1 _)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left powbound he.le]
  obtain ⟨d,hd,eq⟩ := intermediate_value_Icc endpos cf
    (show e ∈ Icc (F 0) (F (4*e)) from ⟨by simpa [F] using he.le,last⟩)
  have dpos : 0 < d := lt_of_le_of_ne hd.1 (by rintro rfl; simp [F] at eq; linarith)
  let l := d^(-1/4:ℝ)
  have hl : 0 < l := Real.rpow_pos_of_pos dpos _
  have key : l^4*d=1 := by
    dsimp [l]
    rw [← Real.rpow_natCast _ 4,← Real.rpow_mul dpos.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_neg dpos.le (1:ℝ),Real.rpow_one,inv_mul_cancel₀ dpos.ne']
  have time_eq : l*(time d/l) = time d := by field_simp
  have eps := incoming_radius_parameter hl key x (time d/l) (by simpa only [time_eq] using (r d hd).1)
  rw [time_eq] at eps
  exact ⟨d,⟨dpos,hd.2⟩,l,hl,key,eps.trans eq⟩

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.exists_prescribed_seam_scale
