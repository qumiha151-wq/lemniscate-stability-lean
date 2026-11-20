import SolitonClassification.SeamRadiusLipschitz
import SolitonClassification.PrescribedIncomingRadius

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set

/-- A compact family of crossings at bounded times can all be realized at
    the same prescribed small incoming radius parameter. The selected seam
    parameters depend jointly continuously on curvature and incoming scale,
    including the frozen boundary, with no differentiability assumption on
    the selected times. -/
theorem continuous_prescribed_seam_scales {C : Set ℝ} (hC : IsCompact C) {D T B : ℝ}
    (hD : 0 < D) (hT : 0 ≤ T) (hB : 0 ≤ B) (small : D*T ≤ 1/2) (τ : ℝ → ℝ → ℝ)
    (continuous_time : Continuous (fun z : C × Icc (0:ℝ) D => τ z.1 z.2))
    (bounded : ∀ c ∈ C, ∀ d ∈ Icc (0:ℝ) D, |τ c d| ≤ T)
    (times : ∀ c ∈ C, ∀ a ∈ Icc (0:ℝ) D, ∀ b ∈ Icc (0:ℝ) D, |τ c a-τ c b| ≤ B*|a-b|) :
    ∃ S ∈ Ioc 0 D, ∃ g : C × Icc (0:ℝ) (S*(1/4)) → ℝ, Continuous g ∧ ∀ z,
      g z ∈ Icc 0 S ∧ g z*radiusFactor z.1 (g z) (τ z.1 (g z)) = z.2 ∧
      (∀ d ∈ Icc 0 S, d*radiusFactor z.1 d (τ z.1 d) = z.2 → d = g z) ∧
      (0 < (z.2:ℝ) → ∃ l > (0:ℝ), l^4*g z = 1 ∧
        ReflectedArc.RadialLayer.eps (solution 1 (restore l (seamData z.1 (g z)).2))
          (τ z.1 (g z)/l) = z.2) := by
  obtain ⟨K,hK,lip⟩ := compact_radiusFactor_lipschitz hC hD.le hT hB small τ bounded times
  let S := min D (1/(8*(1+K)))
  have sPos : 0 < S := lt_min hD (by positivity)
  have sD : S ≤ D := min_le_left _ _
  have sk : S*K ≤ (1/4:ℝ)/2 := by
    have hi : S ≤ 1/(8*(1+K)) := min_le_right _ _
    have H := (le_div_iff₀ (by positivity : 0 < 8*(1+K))).mp hi
    linarith only [H,sPos]
  let a (c : C) (d : ℝ) := radiusFactor c d (τ c d)
  have inD {d : ℝ} (hd : d ∈ Icc (0:ℝ) S) : d ∈ Icc (0:ℝ) D := ⟨hd.1,hd.2.trans sD⟩
  have range (c : C) {d : ℝ} (hd : d ∈ Icc (0:ℝ) S) :
      radiusSq (seamState c d (τ c d)) ∈ Icc (1/4:ℝ) 4 := by
    obtain ⟨l,r⟩ := seamRadius_bounds (c:=c) (inD hd) (bounded _ c.property _ (inD hd)) small
    have eq := seamRadius_sq (c:ℝ) d (τ c d)
    constructor <;> nlinarith
  have ca : Continuous (fun z : C × Icc (0:ℝ) S => a z.1 z.2) := by
    have ct := continuous_time.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk (fun z => inD z.2.property)))
    have cs := continuous_solution.comp (ct.prodMk
      (continuous_seamData.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))))
    have comp (i : Fin 4) := (continuous_apply i).comp cs
    apply (((comp 2).pow 2).add ((comp 3).pow 2)).rpow_const
    intro z
    exact Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) (range z.1 z.2.property).1))
  have lower (c : C) (d : ℝ) (hd : d ∈ Icc (0:ℝ) S) : 1/4 ≤ a c d := by
    obtain ⟨lo,hi⟩ := range c hd
    let A := radiusSq (seamState c d (τ c d))
    have hp : 0 < A := lt_of_lt_of_le (by norm_num) lo
    have cap : A^(2/3:ℝ) ≤ 4 :=
      (Real.rpow_le_rpow hp.le hi (by norm_num)).trans
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
          (by norm_num : (2/3:ℝ) ≤ 1)).trans_eq (Real.rpow_one 4))
    change 1/4 ≤ A^(-2/3:ℝ)
    rw [show (-2/3:ℝ)= -(2/3:ℝ) by ring,Real.rpow_neg hp.le,← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hp _) cap
  obtain ⟨g,hg,spec⟩ := prescribe_radius sPos (by norm_num : (0:ℝ)<1/4) hK sk a ca lower
    (fun c x hx y hy => lip _ c.property _ (inD hx) _ (inD hy))
  refine ⟨S,⟨sPos,sD⟩,g,hg,?_⟩
  intro z
  obtain ⟨hd,e,uniq⟩ := spec z
  refine ⟨hd,e,uniq,?_⟩
  intro pos
  have dpos : 0 < g z := lt_of_le_of_ne hd.1 (by intro eq; rw [←eq,zero_mul] at e; linarith)
  let l := (g z)^(-1/4:ℝ)
  have hl : 0 < l := Real.rpow_pos_of_pos dpos _
  have key : l^4 * g z=1 := by
    dsimp [l]
    rw [← Real.rpow_natCast _ 4,← Real.rpow_mul dpos.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_neg dpos.le (1:ℝ),Real.rpow_one,inv_mul_cancel₀ dpos.ne']
  have te : l*(τ z.1 (g z)/l) = τ z.1 (g z) := by field_simp
  have eps := incoming_radius_parameter hl key (seamData z.1 (g z)).2 (τ z.1 (g z)/l)
    (by rw [te]; exact lt_of_lt_of_le (by norm_num) (range z.1 hd).1)
  rw [te] at eps
  exact ⟨l,hl,key,eps.trans e⟩

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.continuous_prescribed_seam_scales
