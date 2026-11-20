import Migration.ExplicitCutoff
import Migration.EndpointMass

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow
namespace StripCutoff

def partition (a b z : ℝ) : ℝ := max 0 (min 1 ((z-b)/(a-b)))

theorem partition_continuous (a b : ℝ) : Continuous (partition a b) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const _))

theorem partition_mem (a b z : ℝ) : 0 ≤ partition a b z ∧ partition a b z ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem partition_of_high {a b z : ℝ} (hab : b<a) (hz : a ≤ z) : partition a b z = 1 := by
  have h : 1 ≤ (z-b)/(a-b) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  simp [partition,min_eq_left h]

theorem partition_of_low {a b z : ℝ} (hab : b<a) (hz : z ≤ b) : partition a b z = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) (sub_nonneg.mpr hab.le))

end StripCutoff
namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)
open StripCutoff

theorem scaled_mass_lower (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    {a k t : ℝ} (ht : t ∈ I) (hk : k ≠ 0) {r : ℝ → ℝ} (hr : Continuous r)
    (hcover : ∀ z, 0 < k*(z-a) → r z=1)
    {u v : ℝ} (hu : u ∈ Icc 0 c.period) (hv : v ∈ Icc 0 c.period)
    (hbase : H (c.position t u)=a) (hpeak : k*(H (c.position t v)-a)=Real.pi) :
    Real.pi / |k| ≤ c.cutoffMass H (scaled k a r hr hcover).weight t := by
  let Q := fun x => primitive (k*(x-a))/k
  let p := (scaled k a r hr hcover).weight
  have hQ (x) : HasDerivAt Q (p x) x := scaled_primitive_hasDerivAt hk a x
  have hpc : Continuous p := weight_continuous.comp ((continuous_id.sub continuous_const).const_mul k)
  have hn : ∀ z, 0 ≤ p z := fun z => (weight_mem _).1
  have h1 : Q (H (c.position t u))=0 := by simp [Q,hbase,primitive_zero]
  have h2 : Q (H (c.position t v))=Real.pi/2/k := by simp [Q,hpeak,primitive_pi]
  have hab : 2*|Q (H (c.position t v))-Q (H (c.position t u))| ≤ c.cutoffMass H p t := by
    rcases le_total u v with huv|hvu
    · exact c.two_arcs_pay_height_primitive H hH p hpc hn Q hQ ht hu.1 huv hv.2
    · rw [abs_sub_comm]
      exact c.two_arcs_pay_height_primitive H hH p hpc hn Q hQ ht hv.1 hvu hu.2
  rw [h1,h2,sub_zero,abs_div,abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)] at hab
  convert hab using 1
  ring

theorem scaled_mass_zero (H : ℂ →L[ℝ] ℝ) {a k t : ℝ} {r : ℝ → ℝ} (hr : Continuous r)
    (hcover : ∀ z, 0 < k*(z-a) → r z=1)
    (he : ∀ u ∈ Icc 0 c.period, k*(H (c.position t u)-a) ≤ 0) :
    c.cutoffMass H (scaled k a r hr hcover).weight t = 0 := by
  unfold cutoffMass
  calc
    _ = ∫ _u in 0..c.period, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le c.period_pos.le] at hu
      simp only [scaled,weight_of_nonpos (he u hu),zero_mul]
    _ = _ := intervalIntegral.integral_zero

end SmoothPeriodicImmersion
end MigrationGeometry.Flow
