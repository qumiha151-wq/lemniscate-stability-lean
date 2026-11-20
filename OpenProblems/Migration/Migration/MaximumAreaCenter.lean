import Migration.NearRoundConvexDisk
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace MigrationGeometry.Flow

private def triArea (a b c : ℂ) : ℝ :=
  (b.re-a.re)*(c.im-a.im) - (b.im-a.im)*(c.re-a.re)

private theorem area_eq_perp (a b c : ℂ) :
    triArea a b c = inner ℝ (Complex.I*(b-a)) (c-a) := by
  rw [Complex.inner]
  simp only [triArea,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.sub_re,Complex.sub_im,Complex.I_re,Complex.I_im]
  ring

private theorem nonflat_of_width {A : Set ℂ} {W : ℝ} (hW : 0 < W)
    (hwidth : ∀ e : ℂ, ‖e‖=1 → ∃ x ∈ A, ∃ y ∈ A, W ≤ inner ℝ e x-inner ℝ e y) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, triArea a b c ≠ 0 := by
  obtain ⟨a,ha,b,hb,hw⟩ := hwidth 1 (norm_one)
  have hab : b-a ≠ 0 := by intro h; rw [sub_eq_zero.mp h,sub_self] at hw; linarith
  let n := Complex.I*(b-a)
  have hn : 0 < ‖n‖ := norm_pos_iff.mpr (mul_ne_zero Complex.I_ne_zero hab)
  let e := ‖n‖⁻¹ • n
  have he : ‖e‖ = 1 := by simp [e, hn.ne']
  obtain ⟨x,hx,y,hy,hxy⟩ := hwidth e he
  by_cases hax : triArea a b x = 0
  · refine ⟨a,ha,b,hb,y,hy,?_⟩
    intro hay
    rw [area_eq_perp,inner_sub_right] at hax hay
    change inner ℝ n x-inner ℝ n a=0 at hax
    change inner ℝ n y-inner ℝ n a=0 at hay
    dsimp only [e] at hxy
    rw [real_inner_smul_left,real_inner_smul_left,show inner ℝ n x = inner ℝ n y by linarith,
      sub_self] at hxy
    linarith
  · exact ⟨a,ha,b,hb,x,hx,hax⟩

private theorem barycentric_area (a b c z : ℂ) (h : triArea a b c ≠ 0) :
    let α := triArea z b c / triArea a b c
    let β := triArea a z c / triArea a b c
    let η := triArea a b z / triArea a b c
    α+β+η=1 ∧ α • a + β • b + η • c = z := by
  dsimp only
  constructor
  · field_simp [h]
    unfold triArea
    ring
  · apply Complex.ext
    · simp only [Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
      field_simp [h]
      unfold triArea
      ring
    · simp only [Complex.add_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero]
      field_simp [h]
      unfold triArea
      ring

/-- A maximum-area inscribed triangle fixes one centroid with at least
one third of the given lower width in every support direction. -/
theorem exists_center_of_uniform_width {A : Set ℂ} (hA : IsCompact A) {W : ℝ}
    (hW : 0 < W)
    (hwidth : ∀ e : ℂ, ‖e‖=1 → ∃ x ∈ A, ∃ y ∈ A, W ≤ inner ℝ e x-inner ℝ e y) :
    ∃ p : ℂ, ∀ e : ℂ, ‖e‖=1 → ∃ y ∈ A, inner ℝ e p + W/3 ≤ inner ℝ e y := by
  obtain ⟨a₀,ha₀,b₀,hb₀,c₀,hc₀,hflat⟩ := nonflat_of_width hW hwidth
  let F := fun z : ℂ × (ℂ × ℂ) => |triArea z.1 z.2.1 z.2.2|
  have hc : Continuous F := by unfold F triArea; fun_prop
  obtain ⟨⟨a,b,c⟩,habc,hmax⟩ := (hA.prod (hA.prod hA)).exists_isMaxOn
    (show (A ×ˢ (A ×ˢ A)).Nonempty from ⟨(a₀,b₀,c₀),ha₀,hb₀,hc₀⟩) hc.continuousOn
  have Max (x y z : ℂ) (hx : x∈A) (hy : y∈A) (hz : z∈A) :
      |triArea x y z| ≤ |triArea a b c| := hmax (show (x,y,z) ∈ A ×ˢ (A ×ˢ A) from ⟨hx,hy,hz⟩)
  have habc' := lt_of_lt_of_le (abs_pos.mpr hflat) (Max a₀ b₀ c₀ ha₀ hb₀ hc₀)
  have hd := abs_pos.mp habc'
  let p := (1/3:ℝ) • (a+b+c)
  refine ⟨p,?_⟩
  intro e he
  let H : ℂ →L[ℝ] ℝ := innerSL ℝ e
  obtain ⟨v,hv,hvmax⟩ := hA.exists_isMaxOn ⟨a₀,ha₀⟩ H.continuous.continuousOn
  obtain ⟨hi,hhi,lo,hlo,hspread⟩ := hwidth e he
  have hlo_bound : 3*H p - 2*H v ≤ H lo := by
    let D := triArea a b c
    let α := triArea lo b c / D
    let β := triArea a lo c / D
    let η := triArea a b lo / D
    have rat {x : ℝ} (hx : |x| ≤ |D|) : x/D ≤ 1 :=
      (le_abs_self _).trans (by rw [abs_div]; exact (div_le_one habc').mpr hx)
    have h₁ : α ≤ 1 := rat (Max lo b c hlo habc.2.1 habc.2.2)
    have h₂ : β ≤ 1 := rat (Max a lo c habc.1 hlo habc.2.2)
    have h₃ : η ≤ 1 := rat (Max a b lo habc.1 habc.2.1 hlo)
    obtain ⟨hm,hrep⟩ := barycentric_area a b c lo hd
    change α+β+η=1 at hm
    change α • a + β • b + η • c=lo at hrep
    have hcoord := congrArg H hrep
    simp only [map_add,map_smul,smul_eq_mul] at hcoord
    have hp : 3*H p = H a+H b+H c := by simp only [p,map_smul,map_add,smul_eq_mul]; ring
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_left (hvmax habc.1) (sub_nonneg.mpr h₁),
      mul_le_mul_of_nonneg_left (hvmax habc.2.1) (sub_nonneg.mpr h₂),
      mul_le_mul_of_nonneg_left (hvmax habc.2.2) (sub_nonneg.mpr h₃),
      congrArg (fun z => z*H v) hm]
  refine ⟨v,hv,?_⟩
  change W ≤ H hi - H lo at hspread
  change H p + W/3 ≤ H v
  have hMaxHi : H hi ≤ H v := hvmax hhi
  linarith

#print axioms exists_center_of_uniform_width
end MigrationGeometry.Flow
