import Migration.NearRoundEnergy
import Migration.NearRoundDirections

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem near_round_scalar_rate {E L D b S : ℝ}
    (hL : 0 < L) (hE : 0 < E) (hD : 0 ≤ D) (hS : 2 ≤ S)
    (hlen : 2*E*L ≤ S^2+(1/8:ℝ)^2)
    (hforce : b*L ≤ (1/8:ℝ)*(1+(1+(1/8:ℝ))/S)*Real.sqrt L*Real.sqrt D)
    (hvir : E ≤ (1+(1/8:ℝ))*L/S * Real.sqrt L*Real.sqrt D) :
    b ≤ (5*S/32)*D/E^2 := by
  have hSp : 0<S := by linarith
  have hq : (1/8:ℝ)*(1+(1+(1/8:ℝ))/S) ≤ 1/4 := by
    rw [show (1/8:ℝ)*(1+(1+(1/8:ℝ))/S) = (S/8+9/64)/S by field_simp; ring]
    apply (div_le_iff₀ hSp).mpr
    linarith
  have hproduct : E*L ≤ 17*S^2/32 := by nlinarith [sq_nonneg (S-1)]
  have hfb : b*L ≤ 1/4*Real.sqrt L*Real.sqrt D := by
    exact hforce.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg L)) (Real.sqrt_nonneg D))
  have hmul := mul_le_mul hfb hvir hE.le
    (by positivity : 0 ≤ 1/4*Real.sqrt L*Real.sqrt D)
  have hre : (1/4*Real.sqrt L*Real.sqrt D)*
      ((1+(1/8:ℝ))*L/S*Real.sqrt L*Real.sqrt D) = ((9/32:ℝ)*L^2*D)/S := by
    calc
      _ = ((9/32:ℝ)*L*(Real.sqrt L)^2*(Real.sqrt D)^2)/S := by ring
      _ = _ := by rw [Real.sq_sqrt hL.le,Real.sq_sqrt hD]; ring
  rw [hre] at hmul
  have hh := (le_div_iff₀ hSp).mp hmul
  have hh' : (b*E*S)*L ≤ (9/32*L*D)*L := by linarith
  have hh'' := (mul_le_mul_iff_left₀ hL).mp hh'
  have h3 := mul_le_mul_of_nonneg_right hh'' hE.le
  have h4 := mul_le_mul_of_nonneg_right hproduct hD
  apply (le_div_iff₀ (sq_pos_of_pos hE)).mpr
  apply (mul_le_mul_iff_left₀ hSp).mp
  nlinarith [mul_nonneg (sq_nonneg S) hD]

private theorem energy_pos_of_turn {S t : ℝ} (ht : t ∈ I) (hS : 0 < S)
    (hm : c.signedCurvatureIntegral t = S) : 0 < c.bending t := by
  have he := c.oscillation_energy_identity ht hm
  have hp := c.curvatureOscillation_nonneg ht S
  by_contra! h
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h (c.coreLength_pos ht).le, sq_pos_of_pos hS]

/-- The initial material arclength centroid and an explicit radius are
simultaneous lower support bounds in every unit direction. The only data
on the time slab are the signed turning and the L² curvature oscillation.
In particular, no normal surjectivity or centroid drift is an input. -/
theorem fixed_initial_centroid_support (hf : c.IsNormalFEF)
    {s t S : ℝ} (hst : s ≤ t) (hslab : Icc s t ⊆ I) (hS : 2 ≤ S)
    (hm : ∀ v ∈ Icc s t, c.signedCurvatureIntegral v = S)
    (ho : ∀ v ∈ Icc s t, c.curvatureOscillation S v ≤ 1/64)
    (e : ℂ) (he : ‖e‖ = 1) :
    ∃ u ∈ Icc 0 c.period, inner ℝ e (c.arclengthCentroid s) + 9*c.coreLength t/(16*S) ≤
      inner ℝ e (c.position t u) := by
  let H : ℂ →L[ℝ] ℝ := innerSL ℝ e
  have hH : ‖H‖ ≤ 1 := by dsimp [H]; rw [innerSL_apply_norm,he]
  have hs : s ∈ Icc s t := ⟨le_rfl,hst⟩
  have ht : t ∈ Icc s t := ⟨hst,le_rfl⟩
  have hSp : 0<S := by linarith
  have hE (v) (hv : v ∈ Icc s t) := c.energy_pos_of_turn (hslab hv) hSp (hm v hv)
  have hsmall (v) (hv : v ∈ Icc s t) : c.curvatureOscillation S v ≤ (1/8:ℝ)^2 := by
    norm_num
    exact ho v hv
  have hrate (v) (hv : v ∈ Icc s t) : |c.centroidRate H v| ≤
      (5*S/32)*c.localDissipation H (fun _ => 1) v / c.bending v^2 := by
    have hn : 0 ≤ c.localDissipation H (fun _ => 1) v :=
      intervalIntegral.integral_nonneg_of_forall c.period_pos.le
        (fun u => mul_nonneg (sq_nonneg _) (speed_pos (c.immersion v (hslab hv)) u).le)
    apply near_round_scalar_rate (c.coreLength_pos (hslab hv)) (hE v hv) hn hS
    · rw [c.oscillation_energy_identity (hslab hv) (hm v hv)]
      linarith [hsmall v hv]
    · exact c.centroidRate_near_round H hH (hslab hv) hSp (by norm_num) (hsmall v hv)
    · exact c.bending_le_near_round_virial H (hslab hv) hSp (by norm_num) (hsmall v hv)
  have hshift := c.centroid_displacement_of_force_bound hf H hst hslab hE hrate
  have hE0 : 0 ≤ (5*S/32)/c.bending s := by positivity [hE s hs]
  have hEL := c.oscillation_energy_identity (hslab ht) (hm t ht)
  have hnon := c.curvatureOscillation_nonneg (hslab ht) S
  have hsc : (5*S/32)/c.bending t ≤ 5*c.coreLength t/(16*S) := by
    apply (div_le_iff₀ (hE t ht)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos (by norm_num) hSp)).mpr
    nlinarith
  have Hhit := c.near_round_hits_negative_normal (hslab ht) hSp (by norm_num)
    (by norm_num) (hsmall t ht) e he
  obtain ⟨u,hu,hval⟩ := c.radial_support_from_normal H hH (hslab ht) hSp (by norm_num)
    (hsmall t ht) Hhit
  refine ⟨u,hu,?_⟩
  change H (c.arclengthCentroid s) + 9*c.coreLength t/(16*S) ≤ H (c.position t u)
  rw [c.map_arclengthCentroid H (hslab hs)]
  have hneg := (abs_le.mp hshift).1
  linarith [show c.coreLength t*((1-(1/8:ℝ))/S)-5*c.coreLength t/(16*S) =
    9*c.coreLength t/(16*S) by ring]

#print axioms fixed_initial_centroid_support
end MigrationGeometry.Flow.SmoothPeriodicImmersion
