import Lemniscate.PeriodicFiniteProjectionL2

/-! The reduced Bloch polynomial needs only a quadratic-form comparison.
A coarse coefficient error suffices; no sharp intermediate constants are used. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleReducedBlochForm
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (α : ℝ) (f g : circleH4Domain T) : ℂ :=
  let f₀ := circleFixedProjectionH4 T f
  let g₀ := circleFixedProjectionH4 T g
  let f₁ := f-f₀
  let g₁ := g-g₀
  let c : ℂ := ((-4*(2*Real.pi/T)^4:ℝ):ℂ)
  H 2 f₀ g₀+c*(α:ℂ)^2*inner ℂ (f₀:CircleL2 T) (g₀:CircleL2 T)+
    (H 1 f₀ g₁+H 1 f₁ g₀)+(α:ℂ)*(H 2 f₀ g₁+H 2 f₁ g₀)+
    (α:ℂ)^2*(H 3 f₀ g₁+H 3 f₁ g₀)+
    H 0 f₁ g₁+(α:ℂ)*H 1 f₁ g₁+(α:ℂ)^2*H 2 f₁ g₁+
    (α:ℂ)^3*H 3 f₁ g₁+c*(α:ℂ)^4*inner ℂ (f₁:CircleL2 T) (g₁:CircleL2 T)

theorem circle_finite_reduced_form (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (f g : circleH4Domain T) :
    circleReducedBlochForm T (circleFiniteSymmetricCoefficient T h h₁ h₂) α f g =
      circleFiniteBlochPairing T h h₁ h₂ α f g := rfl

private theorem norm_eleven_terms (a b c d e f g h i j k : ℂ) :
    ‖a+b+c+d+e+f+g+h+i+j+k‖ ≤
      ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖+‖f‖+‖g‖+‖h‖+‖i‖+‖j‖+‖k‖ := by
  have h1 := norm_add_le a b
  have h2 := norm_add_le (a+b) c
  have h3 := norm_add_le (a+b+c) d
  have h4 := norm_add_le (a+b+c+d) e
  have h5 := norm_add_le (a+b+c+d+e) f
  have h6 := norm_add_le (a+b+c+d+e+f) g
  have h7 := norm_add_le (a+b+c+d+e+f+g) h
  have h8 := norm_add_le (a+b+c+d+e+f+g+h) i
  have h9 := norm_add_le (a+b+c+d+e+f+g+h+i) j
  have h10 := norm_add_le (a+b+c+d+e+f+g+h+i+j) k
  linarith only [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

set_option maxHeartbeats 1000000 in
theorem circle_reduced_form_difference_bound
    (H HN : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (hH : ∀ j f g, ‖H j f g-HN j f g‖ ≤ (1/2000:ℝ)*‖f‖*‖g‖)
    (α : ℝ) (hα : |α| ≤ 1) (f : circleH4Domain T) :
    ‖circleReducedBlochForm T H α f f-circleReducedBlochForm T HN α f f‖ ≤
      (1/100:ℝ)*‖f‖^2 := by
  let u := circleFixedProjectionH4 T f
  let v := f-u
  have hs := circle_fixed_projection_l2_norm_split T f
  change ‖v‖^2+‖u‖^2 = ‖f‖^2 at hs
  have hu : ‖u‖ ≤ ‖f‖ := by nlinarith only [hs,sq_nonneg ‖v‖,norm_nonneg u,norm_nonneg f]
  have hv : ‖v‖ ≤ ‖f‖ := by nlinarith only [hs,sq_nonneg ‖u‖,norm_nonneg v,norm_nonneg f]
  let term (k : ℕ) (j : Fin 5) (x y : circleH4Domain T) :=
    (α:ℂ)^k*(H j x y-HN j x y)
  have hpow (k : ℕ) : ‖(α:ℂ)^k‖ ≤ 1 := by
    rw [norm_pow]
    have hbase : ‖(α:ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hα
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (α:ℂ)) hbase k
  have hterm (k : ℕ) (j : Fin 5) (x y : circleH4Domain T)
      (hx : ‖x‖ ≤ ‖f‖) (hy : ‖y‖ ≤ ‖f‖) : ‖term k j x y‖ ≤
      (1/2000:ℝ)*‖f‖^2 := by
    dsimp only [term]
    rw [norm_mul]
    have hxy := mul_le_mul hx hy (norm_nonneg _) (norm_nonneg f)
    have he := (hH j x y).trans
      (by nlinarith only [hxy] : (1/2000:ℝ)*‖x‖*‖y‖ ≤ (1/2000:ℝ)*‖f‖^2)
    have hm := mul_le_mul (hpow k) he (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using hm
  have hid : circleReducedBlochForm T H α f f-circleReducedBlochForm T HN α f f =
      term 0 2 u u+term 0 1 u v+term 0 1 v u+term 1 2 u v+term 1 2 v u+
        term 2 3 u v+term 2 3 v u+term 0 0 v v+term 1 1 v v+term 2 2 v v+term 3 3 v v := by
    dsimp only [circleReducedBlochForm,term,u,v]
    ring
  rw [hid]
  have ht := norm_eleven_terms (term 0 2 u u) (term 0 1 u v) (term 0 1 v u)
    (term 1 2 u v) (term 1 2 v u) (term 2 3 u v) (term 2 3 v u)
    (term 0 0 v v) (term 1 1 v v) (term 2 2 v v) (term 3 3 v v)
  have h1 := hterm 0 2 u u hu hu
  have h2 := hterm 0 1 u v hu hv
  have h3 := hterm 0 1 v u hv hu
  have h4 := hterm 1 2 u v hu hv
  have h5 := hterm 1 2 v u hv hu
  have h6 := hterm 2 3 u v hu hv
  have h7 := hterm 2 3 v u hv hu
  have h8 := hterm 0 0 v v hv hv
  have h9 := hterm 1 1 v v hv hv
  have h10 := hterm 2 2 v v hv hv
  have h11 := hterm 3 3 v v hv hv
  nlinarith only [ht,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,sq_nonneg ‖f‖]

end Lemniscate
