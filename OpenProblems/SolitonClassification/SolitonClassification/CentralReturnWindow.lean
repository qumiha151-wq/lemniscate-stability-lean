import SolitonClassification.CentreShotAlignment
import SolitonClassification.CentreCriticalLayer

/-! A bound in the fast arclength variable on returns of a centre shot to
a fixed disk in the central scaling. It includes the entire outer flight up
to the first critical layer. -/
noncomputable section
namespace ClosedSimilarity.OuterStress.Data
open Set

theorem fast_time_le_of_early_radius {δ τ R : ℝ} (z : Data δ)
    (hd : 0<δ) (small : δ≤1/32) (hk : z.K 0=0) (hv : z.V 0=1)
    (hp : z.p 0=0) (hq : z.q 0=0) (ht : τ ∈ Icc (0:ℝ) (1/2))
    (radius : z.p τ^2 + z.q τ^2 ≤ (δ*R)^2) (hR : 0≤R) :
    τ/δ ≤ 72*R+8 := by
  have mono := z.centre_alignment_monotone hd small hk hv hp hq
  have comp := mono (show (0:ℝ)∈Icc (0:ℝ) (1/2) by norm_num) ht ht.1
  have zz : 18*z.along 0+δ*(z.shape 0*z.slope 0)-(0:ℝ)/4=0 := by
    simp [along,radial,shape,hk,hv,hp,hq]
  dsimp only at comp
  rw [zz] at comp
  have a := (z.centre_bounds hd hk hv hp hq ht.1).2
  have ap : 0<z.amplitude τ := by
    have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
    nlinarith
  have rs := z.radius_sq τ ap
  have alongBound : z.along τ ≤ δ*R := by
    apply (le_abs_self _).trans
    apply le_of_sq_le_sq _ (mul_nonneg hd.le hR)
    rw [sq_abs]
    nlinarith [sq_nonneg (z.across τ)]
  have osc := (z.normalized_rates τ ap hd).oscillator
  have U : |z.shape τ| ≤ 2 := le_of_sq_le_sq
    (by rw [sq_abs]; nlinarith [sq_nonneg (z.slope τ),sq_nonneg ((z.shape τ)^2/2-1)]) (by norm_num)
  have w : |z.slope τ| ≤ 1 := le_of_sq_le_sq
    (by rw [sq_abs]; nlinarith [sq_nonneg ((z.shape τ)^2/2)]) zero_le_one
  have prod : z.shape τ*z.slope τ ≤ 2 := (le_abs_self _).trans (by
    rw [abs_mul]; simpa using mul_le_mul U w (abs_nonneg _) (by norm_num))
  apply (div_le_iff₀ hd).mpr
  nlinarith only [comp,alongBound,mul_le_mul_of_nonneg_left prod hd.le]

/-- The late part of this same certified outer flight stays outside every
fixed central-scale disk once the centre marker is sufficiently large. -/
theorem fast_time_le_on_critical_flight (R : ℝ) (hR : 0≤R) :
    ∃ L₀≥1, ∀ L≥L₀, ∀ {δ : ℝ} (z : Data δ), 0<δ → δ≤1/(32*L) →
      δ*R≤1/1200 → z.K 0=0 → z.V 0=1 → z.p 0=0 → z.q 0=0 →
      ∃ T∈Icc (1/2:ℝ) 10000, z.root T^3=L*δ ∧
        ∀ τ∈Icc 0 T, z.p τ^2+z.q τ^2≤(δ*R)^2 → τ/δ≤72*R+8 := by
  obtain ⟨L₀,hL₀,C,_,crit⟩ := reaches_critical_layer
  refine ⟨L₀,hL₀,?_⟩
  intro L hl δ z hd small disk hk hv hp hq
  obtain ⟨T,hT,layer,region⟩ := crit L hl z hd small hk hv hp hq
  refine ⟨T,hT,layer,?_⟩
  intro τ hτ radius
  have one : 1≤L := hL₀.trans hl
  have small' : δ≤1/32 := by
    apply small.trans
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<32)
    linarith
  by_cases first : τ≤1/2
  · exact z.fast_time_le_of_early_radius hd small' hk hv hp hq ⟨hτ.1,first⟩ radius hR
  · have h := region τ ⟨le_of_not_ge first,hτ.2⟩
    have rpos : 0<z.root τ := by
      by_contra! hn
      have hh := mul_pos (by linarith : 0<L) hd
      have : z.root τ=0 := le_antisymm hn (Real.sqrt_nonneg _)
      rw [this] at h
      nlinarith only [hh,h.2.2.1]
    have pos := Real.sqrt_pos.mp rpos
    have rs := z.radius_sq τ pos
    have big : δ*R<z.along τ := disk.trans_lt h.1
    have sq := sq_lt_sq' (by linarith [mul_nonneg hd.le hR]) big
    nlinarith [sq_nonneg (z.across τ)]

end ClosedSimilarity.OuterStress.Data
#print axioms ClosedSimilarity.OuterStress.Data.fast_time_le_on_critical_flight
