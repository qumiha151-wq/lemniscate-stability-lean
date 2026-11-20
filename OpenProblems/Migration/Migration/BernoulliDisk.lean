import Migration.EscapingHulls
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
open Set
namespace MigrationGeometry.BernoulliDisk

/-- The rational trigonometric parametrization in the supplied manuscript. -/
def profile (θ : ℝ) : ℂ :=
  ⟨Real.cos θ / (1+(Real.sin θ)^2),
    Real.cos θ * Real.sin θ / (1+(Real.sin θ)^2)⟩

def radius : ℝ := Real.sqrt 2 / 4

theorem radius_pos : 0 < radius := by unfold radius; positivity

private theorem inner_xy (z w : ℂ) :
    inner ℝ z w = z.re*w.re + z.im*w.im := by
  simp only [Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

private theorem circle_norm {x y : ℝ} (h : x^2+y^2=1) : ‖(⟨x,y⟩ : ℂ)‖=1 := by
  have hn := Complex.normSq_eq_norm_sq (⟨x,y⟩ : ℂ)
  simp only [Complex.normSq_apply] at hn
  nlinarith [norm_nonneg (⟨x,y⟩ : ℂ)]

private theorem corner {a b : ℝ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    (⟨a*Real.sqrt 3*radius, b*radius⟩ : ℂ) ∈ range profile := by
  let x := a * Real.sqrt 2 * Real.sqrt 3 / 3
  let y := a * b * Real.sqrt 3 / 3
  have ha2 : a^2=1 := by rcases ha with h|h <;> rw [h] <;> norm_num
  have hb2 : b^2=1 := by rcases hb with h|h <;> rw [h] <;> norm_num
  have h2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hy : y^2=1/3 := by dsimp [y]; rw [div_pow,mul_pow,mul_pow,ha2,hb2,h3]; norm_num
  have hx : x^2=2/3 := by dsimp [x]; rw [div_pow,mul_pow,mul_pow,ha2,h2,h3]; norm_num
  let z : ℂ := ⟨x,y⟩
  have hn : ‖z‖=1 := circle_norm (by linarith [hx,hy])
  have hcos : Real.cos z.arg=x := by
    rw [Complex.cos_arg (norm_ne_zero_iff.mp (by rw [hn]; norm_num)),hn,div_one]
  have hsin : Real.sin z.arg=y := by rw [Complex.sin_arg,hn,div_one]
  refine ⟨z.arg,?_⟩
  apply Complex.ext
  · change Real.cos z.arg / (1+(Real.sin z.arg)^2) = _
    rw [hcos,hsin,hy]
    dsimp [x,radius]
    ring
  · change Real.cos z.arg * Real.sin z.arg / (1+(Real.sin z.arg)^2) = _
    rw [hcos,hsin,hy]
    dsimp [x,y,radius]
    calc
      _ = a^2*b*Real.sqrt 2*(Real.sqrt 3)^2/12 := by ring
      _ = _ := by rw [ha2,h3]; ring

private theorem sign_choice (u : ℝ) : ∃ a : ℝ, (a=1 ∨ a= -1) ∧ u*a = |u| := by
  by_cases hu : 0 ≤ u
  · exact ⟨1,Or.inl rfl,by simp [abs_of_nonneg hu]⟩
  · exact ⟨-1,Or.inr rfl,by simp [abs_of_neg (lt_of_not_ge hu)]⟩

theorem reference_support (e : ℂ) (he : ‖e‖=1) :
    ∃ z ∈ range profile, radius ≤ inner ℝ e z := by
  obtain ⟨a,ha,hx⟩ := sign_choice e.re
  obtain ⟨b,hb,hy⟩ := sign_choice e.im
  refine ⟨_,corner ha hb,?_⟩
  rw [inner_xy]
  change radius ≤ e.re*(a*Real.sqrt 3*radius)+e.im*(b*radius)
  rw [show e.re*(a*Real.sqrt 3*radius)+e.im*(b*radius) =
    (e.re*a*Real.sqrt 3 + e.im*b)*radius by ring,hx,hy]
  have hab := Complex.norm_le_abs_re_add_abs_im e
  rw [he] at hab
  have hroot : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (show 0≤(3:ℝ) by norm_num),Real.sqrt_nonneg 3]
  exact le_mul_of_one_le_left radius_pos.le
    (hab.trans (add_le_add (le_mul_of_one_le_right (abs_nonneg _) hroot) le_rfl))

theorem reference_ceiling (θ : ℝ) : (profile θ).im ≤ radius := by
  let v := Real.sin θ
  let u := Real.cos θ
  have hc : v^2+u^2=1 := Real.sin_sq_add_cos_sq θ
  have hroot : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hsq : (u*v)^2 ≤ (radius*(1+v^2))^2 := by
    unfold radius
    rw [mul_pow,mul_pow,div_pow,hroot]
    nlinarith [sq_nonneg (1-3*v^2),congrArg (fun t : ℝ => t*v^2) hc]
  change u*v/(1+v^2) ≤ radius
  apply (div_le_iff₀ (by positivity)).2
  exact le_of_sq_le_sq hsq (mul_nonneg radius_pos.le (by positivity))

theorem reference_compact : IsCompact (range profile) := by
  have hp : Function.Periodic profile (2*Real.pi) := by intro θ; simp [profile]
  have hP : 0 < 2*Real.pi := by positivity
  have hc : Continuous profile := by
    apply Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun θ : ℝ => (Real.cos θ/(1+(Real.sin θ)^2),
        Real.cos θ*Real.sin θ/(1+(Real.sin θ)^2))) from ?_)
    fun_prop (disch := intro x; positivity)
  have he : range profile = profile '' Icc 0 (2*Real.pi) := by
    ext z
    constructor
    · rintro ⟨θ,rfl⟩
      refine ⟨toIcoMod hP 0 θ,Ico_subset_Icc_self (toIcoMod_mem_Ico' hP θ),?_⟩
      rw [← self_sub_toIcoDiv_zsmul hP 0 θ]
      exact hp.sub_zsmul_eq _
    · rintro ⟨θ,_,rfl⟩
      exact mem_range_self θ
  rw [he]
  exact isCompact_Icc.image hc

end MigrationGeometry.BernoulliDisk
