import Migration.BernoulliDisk
import Migration.NearRoundConvexDisk

noncomputable section
open Set
open Filter
open scoped Topology
namespace MigrationGeometry.BernoulliDisk

/-- Both distances are physical. The dimensionless shape error is multiplied
by the physical scale. A new isometry can be used on each time slice. -/
def Tracks (K : Set ℂ) (p : ℂ) (ρ ε : ℝ) : Prop :=
  ∃ R : ℂ ≃ₗᵢ[ℝ] ℂ,
    (∀ θ : ℝ, ∃ y ∈ K, dist y (p+ρ • R (profile θ)) ≤ ρ*ε) ∧
    (∀ y ∈ K, ∃ θ : ℝ, dist y (p+ρ • R (profile θ)) ≤ ρ*ε)

/-- A single uniform estimate on any parametrization of a finite cover is
enough. Only its range and the range of the actual slice enter the proof. -/
theorem tracks_of_parametrized_error {α : Type*} (X Y : α → ℂ)
    (hY : range Y = range profile) (p : ℂ) (ρ ε : ℝ) (R : ℂ ≃ₗᵢ[ℝ] ℂ)
    (h : ∀ u, dist (X u) (p+ρ • R (Y u)) ≤ ρ*ε) : Tracks (range X) p ρ ε := by
  refine ⟨R,?_,?_⟩
  · intro θ
    obtain ⟨u,hu⟩ := hY ▸ mem_range_self (f := profile) θ
    exact ⟨X u,mem_range_self u,hu ▸ h u⟩
  · rintro _ ⟨u,rfl⟩
    obtain ⟨θ,hθ⟩ := hY ▸ mem_range_self (f := Y) u
    exact ⟨θ,hθ ▸ h u⟩

private theorem directional_error {e y z : ℂ} (he : ‖e‖=1) {v : ℝ} (hd : dist y z ≤ v) :
    inner ℝ e z - v ≤ inner ℝ e y ∧ inner ℝ e y ≤ inner ℝ e z + v := by
  have h1 := real_inner_le_norm e (y-z)
  have h2 := real_inner_le_norm e (z-y)
  rw [inner_sub_right,he,one_mul,← dist_eq_norm] at h1 h2
  rw [dist_comm z y] at h2
  constructor <;> linarith

private theorem closed_disk_of_support {K : Set ℂ} (hK : IsCompact K) {p : ℂ} {r : ℝ}
    (hr : 0<r) (hs : ∀ e : ℂ, ‖e‖=1 → ∃ y ∈ K, inner ℝ e p+r ≤ inner ℝ e y) :
    Metric.closedBall p r ⊆ convexHull ℝ K := by
  rw [← closure_ball p hr.ne']
  apply closure_minimal _ (SimilarityHull.compact_convexHull hK).isClosed
  intro x hx
  exact Flow.closedBall_subset_convexHull_of_directional_margin (Metric.mem_ball.mp hx)
    hs (Metric.mem_closedBall.mpr le_rfl)

/-- Sharp lower and upper bounds on the centred inradius for a uniformly
approximated physical slice. The lower bound includes the boundary circle. -/
theorem disk_squeeze {K : Set ℂ} (hK : IsCompact K) {p : ℂ} {ρ ε : ℝ}
    (hρ : 0<ρ) (hε : ε < radius) (hfit : Tracks K p ρ ε) :
    Metric.closedBall p (ρ*(radius-ε)) ⊆ convexHull ℝ K ∧
    ∀ d : ℝ, 0 ≤ d → Metric.closedBall p d ⊆ convexHull ℝ K → d ≤ ρ*(radius+ε) := by
  obtain ⟨R,hfrom,hto⟩ := hfit
  constructor
  · apply closed_disk_of_support hK (mul_pos hρ (sub_pos.mpr hε))
    intro e he
    obtain ⟨_,⟨θ,rfl⟩,hs⟩ := reference_support (R.symm e) (by simpa using he)
    obtain ⟨y,hy,hd⟩ := hfrom θ
    have h := (directional_error he hd).1
    have hrot : inner ℝ e (R (profile θ)) = inner ℝ (R.symm e) (profile θ) := by
      simpa using R.inner_map_map (R.symm e) (profile θ)
    rw [inner_add_right,real_inner_smul_right,hrot] at h
    exact ⟨y,hy,by linarith [mul_le_mul_of_nonneg_left hs hρ.le]⟩
  · intro d hd hball
    let e := R Complex.I
    have he : ‖e‖=1 := by simp [e]
    let f : ℂ →L[ℝ] ℝ := innerSL ℝ e
    have hhalf : convexHull ℝ K ⊆ f ⁻¹' Iic (f p + ρ*(radius+ε)) := by
      apply convexHull_min _ ((convex_Iic _).linear_preimage f.toLinearMap)
      intro y hy
      obtain ⟨θ,hθ⟩ := hto y hy
      have hh := (directional_error he hθ).2
      have hrot : inner ℝ e (R (profile θ)) = (profile θ).im := by
        rw [show e = R Complex.I from rfl,R.inner_map_map]
        simp [Complex.inner,Complex.mul_re]
      rw [inner_add_right,real_inner_smul_right,hrot] at hh
      change inner ℝ e y ≤ inner ℝ e p + ρ*(radius+ε)
      linarith [mul_le_mul_of_nonneg_left (reference_ceiling θ) hρ.le]
    have hm : p+d • e ∈ Metric.closedBall p d := by
      simp [Metric.mem_closedBall,dist_eq_norm,Real.norm_eq_abs,abs_of_nonneg hd,he]
    have hu := hhalf (hball hm)
    change inner ℝ e (p+d • e) ≤ inner ℝ e p + ρ*(radius+ε) at hu
    rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,he] at hu
    linarith

/-- The exact optimally sized disk for the original trigonometric image. -/
theorem reference_disk_exact :
    Metric.closedBall (0:ℂ) radius ⊆ convexHull ℝ (range profile) ∧
    ∀ d : ℝ, 0 ≤ d → Metric.closedBall (0:ℂ) d ⊆ convexHull ℝ (range profile) → d ≤ radius := by
  have ht := tracks_of_parametrized_error profile profile rfl 0 1 0
    (LinearIsometryEquiv.refl ℝ ℂ) (by simp)
  simpa using disk_squeeze reference_compact (by norm_num : (0:ℝ)<1) radius_pos ht

/-- Any two slices share a fixed positive disk, even with independent
choices of rotations and parameter maps, whenever scales have lower bound a. -/
theorem all_time_common_disk {K : ℝ → Set ℂ} {p : ℂ} {ρ : ℝ → ℝ} {a ε : ℝ}
    (ha : 0<a) (hε : ε<radius) (hρ : ∀ t, 0≤t → a≤ρ t)
    (hK : ∀ t, 0≤t → IsCompact (K t)) (hfit : ∀ t, 0≤t → Tracks (K t) p (ρ t) ε) :
    (∀ t, 0≤t → Metric.closedBall p (a*(radius-ε)) ⊆ convexHull ℝ (K t)) ∧
    (∀ s, 0≤s → ∀ t, 0≤t → ¬SimilarityHull.separated (K s) (K t)) := by
  have incl (t : ℝ) (ht : 0≤t) : Metric.closedBall p (a*(radius-ε)) ⊆ convexHull ℝ (K t) :=
    (Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (hρ t ht) (sub_nonneg.mpr hε.le))).trans
      (disk_squeeze (hK t ht) (ha.trans_le (hρ t ht)) hε (hfit t ht)).1
  have hm : p ∈ Metric.closedBall p (a*(radius-ε)) := by
    simp [Metric.mem_closedBall, (mul_pos ha (sub_pos.mpr hε)).le]
  exact ⟨incl,fun s hs t ht => SimilarityHull.not_separated_of_common_hull (incl s hs hm) (incl t ht hm)⟩

/-- The normalized uniform estimate used in orbital stability, converted
to the physical image with fixed centre p. -/
theorem tracks_of_normalized_error {α : Type*} (X Y : α → ℂ)
    (hY : range Y = range profile) (p : ℂ) {ρ ε : ℝ} (hρ : 0<ρ) (R : ℂ ≃ₗᵢ[ℝ] ℂ)
    (h : ∀ u, dist (ρ⁻¹ • (X u-p)) (R (Y u)) ≤ ε) : Tracks (range X) p ρ ε := by
  apply tracks_of_parametrized_error X Y hY p ρ ε R
  intro u
  have hn := mul_le_mul_of_nonneg_left (h u) hρ.le
  rw [dist_eq_norm] at hn ⊢
  have he : X u-(p+ρ • R (Y u)) = ρ • (ρ⁻¹ • (X u-p)-R (Y u)) := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ hρ.ne',one_smul]; abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
  exact hn

def centeredInradius (K : Set ℂ) (p : ℂ) : ℝ :=
  sSup {d : ℝ | 0≤d ∧ Metric.closedBall p d ⊆ convexHull ℝ K}

theorem normalized_inradius_error {K : Set ℂ} (hK : IsCompact K) {p : ℂ} {ρ ε : ℝ}
    (hρ : 0<ρ) (hε : ε<radius) (hfit : Tracks K p ρ ε) :
    |centeredInradius K p / ρ-radius| ≤ ε := by
  obtain ⟨hl,hu⟩ := disk_squeeze hK hρ hε hfit
  let D := {d : ℝ | 0≤d ∧ Metric.closedBall p d ⊆ convexHull ℝ K}
  have hm : ρ*(radius-ε) ∈ D := ⟨(mul_pos hρ (sub_pos.mpr hε)).le,hl⟩
  have hb : ∀ d ∈ D, d ≤ ρ*(radius+ε) := fun d hd => hu d hd.1 hd.2
  have hlo : ρ*(radius-ε) ≤ centeredInradius K p := le_csSup ⟨_,hb⟩ hm
  have hhi : centeredInradius K p ≤ ρ*(radius+ε) := csSup_le ⟨_,hm⟩ hb
  have hlo' : radius-ε ≤ centeredInradius K p/ρ :=
    (le_div_iff₀ hρ).2 (by simpa [mul_comm] using hlo)
  have hhi' : centeredInradius K p/ρ ≤ radius+ε :=
    (div_le_iff₀ hρ).2 (by simpa [mul_comm] using hhi)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Rotations need not converge for convergence of the normalized inradius. -/
theorem normalized_inradius_tendsto {K : ℝ → Set ℂ} {p : ℂ} {ρ ε : ℝ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hK : ∀ᶠ t in atTop, IsCompact (K t))
    (hρ : ∀ᶠ t in atTop, 0 < ρ t) (hfit : ∀ᶠ t in atTop, Tracks (K t) p (ρ t) (ε t)) :
    Tendsto (fun t => centeredInradius (K t) p / ρ t) atTop (𝓝 radius) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [hK,hρ,hfit,hε.eventually (gt_mem_nhds radius_pos),
    hε.eventually (gt_mem_nhds hδ)] with t hKt hρt hft het hδt
  exact (normalized_inradius_error hKt hρt het hft).trans_lt hδt

/-- The physical scale (a^4+30t)^(1/4) in the manuscript. -/
def physicalScale (a t : ℝ) := Real.sqrt (Real.sqrt (a^4+30*t))

theorem initial_scale_le {a t : ℝ} (ha : 0≤a) (ht : 0≤t) : a ≤ physicalScale a t := by
  have h := Real.sqrt_le_sqrt (show (a^2)^2 ≤ a^4+30*t by nlinarith)
  rw [Real.sqrt_sq (sq_nonneg a)] at h
  have h' := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha] at h'

theorem cover_range (M : ℕ) (hM : 0<M) :
    range (fun θ : ℝ => profile (M*θ)) = range profile := by
  have h : (M : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hM)
  ext z
  constructor
  · rintro ⟨θ,rfl⟩
    exact mem_range_self _
  · rintro ⟨θ,rfl⟩
    exact ⟨θ/M,congrArg profile (by field_simp)⟩

/-- Orbital-stability-to-migration implication at physical times. X may
use a separate parametrization at every time. The translation p is fixed. -/
theorem near_bernoulli_all_times {α : Type*} (X : ℝ → α → ℂ) (Y : α → ℂ)
    (hY : range Y=range profile) {p : ℂ} {a C deviation : ℝ} (ha : 0<a)
    (hsmall : C*Real.sqrt deviation < radius)
    (hK : ∀ t, 0≤t → IsCompact (range (X t)))
    (horbit : ∀ t, 0≤t → ∃ R : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ u,
      dist ((physicalScale a t)⁻¹ • (X t u-p)) (R (Y u)) ≤ C*Real.sqrt deviation) :
    (∀ t, 0≤t → Metric.closedBall p (physicalScale a t*(radius-C*Real.sqrt deviation)) ⊆
      convexHull ℝ (range (X t))) ∧
    (∀ t, 0≤t → Metric.closedBall p (a*(radius-C*Real.sqrt deviation)) ⊆
      convexHull ℝ (range (X t))) ∧
    (∀ s, 0≤s → ∀ t, 0≤t → ¬SimilarityHull.separated (range (X s)) (range (X t))) := by
  have hρ (t : ℝ) (ht : 0≤t) := initial_scale_le ha.le ht
  have hfit (t : ℝ) (ht : 0≤t) : Tracks (range (X t)) p (physicalScale a t) (C*Real.sqrt deviation) := by
    obtain ⟨R,h⟩ := horbit t ht
    exact tracks_of_normalized_error (X t) Y hY p (ha.trans_le (hρ t ht)) R h
  exact ⟨fun t ht => (disk_squeeze (hK t ht) (ha.trans_le (hρ t ht)) hsmall (hfit t ht)).1,
    all_time_common_disk ha hsmall hρ hK hfit⟩

end MigrationGeometry.BernoulliDisk
