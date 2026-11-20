import SolitonClassification.FrozenSeamReflection
import SolitonClassification.SupportFlowContinuity

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set FrozenStress

def seam (c : ℝ) : Orbit := (exists_frozen_seam c).choose

theorem seam_initial (c : ℝ) :
    (seam c).k 0 = c ∧ (seam c).v 0 = 0 ∧ (seam c).p 0 = 1 ∧ (seam c).q 0 = 0 :=
  (exists_frozen_seam c).choose_spec

def coords (z : Orbit) (s : ℝ) : Phase := ![z.k s,z.v s,z.p s,z.q s]

lemma seam_solution (c : ℝ) : coords (seam c) = solution 0 ![c,0,1,0] := by
  let z := seam c
  obtain ⟨hk,hv,hp,hq⟩ := seam_initial c
  apply (exists_unique_solution 0 ![c,0,1,0]).unique _ ⟨solution_zero _ _,solution_derivative _ _⟩
  refine ⟨by simp [coords,hk,hv,hp,hq],?_⟩
  intro s
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact z.dk s
  · exact z.dv s
  · exact z.dp s
  · simpa [coords,rhs] using z.dq s

theorem continuous_seam_coordinates : Continuous (fun y : ℝ × ℝ => coords (seam y.2) y.1) := by
  simp only [seam_solution]
  have h : Continuous (fun y : ℝ × ℝ => ((y.1,(0,![y.2,0,1,0])) : ℝ × Data)) := by
    apply continuous_fst.prodMk
    apply continuous_const.prodMk
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact continuous_solution.comp h

theorem continuous_seam_transverse : Continuous (fun y : ℝ × ℝ => (seam y.2).transverse y.1) := by
  have h (i : Fin 4) := (continuous_apply i).comp continuous_seam_coordinates
  exact ((((h 0).pow 2).div_const 2).mul (h 2)).sub ((h 1).mul (h 3))

theorem seam_radial_strict (c : ℝ) {t : ℝ} (ht : 0 < t) : (seam c).radial t < 0 := by
  let z := seam c
  obtain ⟨_,hv,hp,hq⟩ := seam_initial c
  have hz : z.radial 0 = 0 := by simp [Orbit.radial,z,hv,hq]
  have hm : Antitone z.radial := antitone_of_deriv_nonpos
    (fun u => (z.radial_hasDerivAt u).differentiableAt)
    (fun u => by rw [(z.radial_hasDerivAt u).deriv]; exact neg_nonpos.mpr (sq_nonneg _))
  by_contra! hn
  have flat (u : ℝ) (hu : u ∈ Icc 0 t) : z.radial u = 0 :=
    le_antisymm ((hm hu.1).trans_eq hz) (hn.trans (hm hu.2))
  have h0 : (0:ℝ) ∈ Icc 0 t := ⟨le_rfl,ht.le⟩
  have hd : HasDerivWithinAt z.radial 0 (Icc 0 t) 0 :=
    (hasDerivWithinAt_const 0 (Icc 0 t) (0:ℝ)).congr_of_mem flat h0
  have hu := uniqueDiffOn_Icc ht 0 h0
  have eq := ((z.radial_hasDerivAt 0).hasDerivWithinAt.derivWithin hu).symm.trans (hd.derivWithin hu)
  change -(seam c).p 0 ^ 2 = 0 at eq
  rw [hp] at eq
  norm_num at eq

/-- Opposite signs at the endpoints of a seam family force simultaneous
vanishing of the transverse stress on two opposite arclength sections. The
radial stresses at those sections are strictly nonzero with opposite signs. -/
theorem transverse_zero_on_opposite_sections {a b t : ℝ} (hab : a < b) (ht : 0 < t)
    (ha : (seam a).root t * (seam a).across t < 0)
    (hb : 0 < (seam b).root t * (seam b).across t) :
    ∃ c ∈ Ioo a b, (seam c).transverse t = 0 ∧ (seam c).transverse (-t) = 0 ∧
      (seam c).radial t < 0 ∧ 0 < (seam c).radial (-t) := by
  have sign (c : ℝ) : 0 < (seam c).amplitude t := by
    have eq := (seam c).stress_unit t
    have r := seam_radial_strict c ht
    nlinarith [show 0 ≤ (seam c).amplitude t from Real.sqrt_nonneg _,
      sq_nonneg ((seam c).transverse t),sq_pos_of_neg r]
  have rt (c : ℝ) : 0 < (seam c).root t := Real.sqrt_pos.mpr (sign c)
  have hlo : (seam a).transverse t < 0 := by
    by_contra! h
    exact (not_lt_of_ge (mul_nonneg (rt a).le (div_nonneg h (sign a).le))) ha
  have hhi : 0 < (seam b).transverse t := by
    by_contra! h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (rt b).le
      (div_nonpos_of_nonpos_of_nonneg h (sign b).le))) hb
  have hc : Continuous (fun c : ℝ => (seam c).transverse t) :=
    continuous_seam_transverse.comp (continuous_const.prodMk continuous_id)
  obtain ⟨c,hc,he⟩ := intermediate_value_Ioo hab.le hc.continuousOn (show (0:ℝ) ∈
    Ioo ((seam a).transverse t) ((seam b).transverse t) from ⟨hlo,hhi⟩)
  obtain ⟨_,hv,_,hq⟩ := seam_initial c
  obtain ⟨k,v,p,q⟩ := (seam c).seam_reflection hv hq t
  have hrad := ((seam c).seam_impact_radial_parity hv hq t).2
  have neg := seam_radial_strict c ht
  refine ⟨c,hc,he,?_,neg,by linarith⟩
  simpa [Orbit.transverse,k,v,p,q] using he

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.seam_radial_strict
#print axioms ClosedSimilarity.GlobalSupport.transverse_zero_on_opposite_sections
