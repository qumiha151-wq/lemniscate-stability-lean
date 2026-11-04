import Lemniscate.NormalGraphGeometry

/-! The geometric rotation term of a normal graph.

The unit normal is the actual derivative rotated by i and divided by its
speed. The prefactor is exactly the speed divided by 1-kh, as in the
normal-graph flow equation. Only first derivatives are required.
-/
noncomputable section
namespace Lemniscate
open Complex
open scoped ComplexConjugate

/-- The infinitesimal rotation of the actual graph has height component
`b + (eta+h) h_s / (1-kh)`. The normal in this identity is formed from the
actual derivative, and is proved to have unit length. -/
theorem normal_graph_rotation_height
    (β t n : ℝ → ℂ) (k h h₁ : ℝ → ℝ) (s : ℝ)
    (hβ : HasDerivAt β (t s) s)
    (hn : HasDerivAt n (-(k s:ℂ)*t s) s)
    (hh : HasDerivAt h (h₁ s) s)
    (htunit : ‖t s‖ = 1) (hnormal : n s = I*t s)
    (hregular : 0 < 1-k s*h s) :
    let γ := normalGraphCurve β n h
    let A := 1-k s*h s
    let ν := I*deriv γ s/(‖deriv γ s‖:ℂ)
    deriv γ s ≠ 0 ∧ ‖ν‖ = 1 ∧
      (‖deriv γ s‖/A)*(conj (I*γ s)*ν).re =
        (conj (t s)*β s).re+
          ((conj (t s)*β s).im+h s)*h₁ s/A := by
  let γ := normalGraphCurve β n h
  let A : ℝ := 1-k s*h s
  let B : ℝ := h₁ s
  let V : ℂ := (A:ℂ)*t s+(B:ℂ)*n s
  have hγ : HasDerivAt γ V s := by
    convert! hβ.add (hh.ofReal_comp.mul hn) using 1 <;>
      dsimp only [γ,normalGraphCurve,V,A,B] <;> push_cast <;> ring
  have hunit : conj (t s)*t s = 1 := by
    rw [Complex.conj_mul',htunit]
    norm_num
  have htzero : t s ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [htunit]
    exact one_ne_zero
  have hA : A ≠ 0 := ne_of_gt hregular
  have hVframe : V = ((A:ℂ)+I*(B:ℂ))*t s := by
    dsimp only [V]
    rw [hnormal]
    ring
  have hVzero : V ≠ 0 := by
    rw [hVframe]
    apply mul_ne_zero _ htzero
    intro hz
    apply hA
    have hre := congrArg Complex.re hz
    simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
      sub_zero,add_zero,Complex.zero_re] using hre
  have hγzero : deriv γ s ≠ 0 := by rw [hγ.deriv]; exact hVzero
  have hspeed : ‖deriv γ s‖ ≠ 0 := norm_ne_zero_iff.mpr hγzero
  have hcoord : conj (t s)*γ s = conj (t s)*β s+I*(h s:ℂ) := by
    dsimp only [γ,normalGraphCurve]
    rw [hnormal]
    calc
      conj (t s)*(β s+(h s:ℂ)*(I*t s)) =
          conj (t s)*β s+I*(h s:ℂ)*(conj (t s)*t s) := by ring
      _ = conj (t s)*β s+I*(h s:ℂ) := by rw [hunit,mul_one]
  have hcoordconj : conj (γ s)*t s =
      conj (conj (t s)*β s)-I*(h s:ℂ) := by
    calc
      conj (γ s)*t s = conj (conj (t s)*γ s) := by
        simp only [map_mul,conj_conj]
        ring
      _ = conj (conj (t s)*β s)-I*(h s:ℂ) := by
        rw [hcoord]
        simp only [map_add,map_mul,Complex.conj_I,Complex.conj_ofReal]
        ring
  have hnum : (conj (γ s)*V).re =
      A*(conj (t s)*β s).re+((conj (t s)*β s).im+h s)*B := by
    rw [hVframe]
    rw [show conj (γ s)*(((A:ℂ)+I*(B:ℂ))*t s) =
      ((A:ℂ)+I*(B:ℂ))*(conj (γ s)*t s) by ring,hcoordconj]
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im,Complex.I_re,Complex.I_im,
      zero_mul,mul_zero,one_mul,mul_one,add_zero,zero_add,sub_zero,zero_sub]
    ring
  have hpair : (conj (I*γ s)*(I*deriv γ s/(‖deriv γ s‖:ℂ))).re =
      (A*(conj (t s)*β s).re+((conj (t s)*β s).im+h s)*B)/‖deriv γ s‖ := by
    rw [show conj (I*γ s)*(I*deriv γ s/(‖deriv γ s‖:ℂ)) =
      (conj (γ s)*deriv γ s)/(‖deriv γ s‖:ℂ) by
        rw [map_mul,Complex.conj_I]
        calc
          (-I*conj (γ s))*(I*deriv γ s/(‖deriv γ s‖:ℂ)) =
              (-I*I)*(conj (γ s)*deriv γ s)/(‖deriv γ s‖:ℂ) := by ring
          _ = (conj (γ s)*deriv γ s)/(‖deriv γ s‖:ℂ) := by
            rw [neg_mul,Complex.I_mul_I,neg_neg,one_mul]]
    rw [Complex.div_ofReal_re,hγ.deriv,hnum]
  refine ⟨hγzero,?_,?_⟩
  · change ‖I*deriv γ s/(‖deriv γ s‖:ℂ)‖ = 1
    rw [norm_div,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (deriv γ s)),one_mul,div_self hspeed]
  · change (‖deriv γ s‖/A)*
      (conj (I*γ s)*(I*deriv γ s/(‖deriv γ s‖:ℂ))).re = _
    rw [hpair]
    change (‖deriv γ s‖/A)*
      ((A*(conj (t s)*β s).re+((conj (t s)*β s).im+h s)*B)/‖deriv γ s‖) =
      (conj (t s)*β s).re+((conj (t s)*β s).im+h s)*B/A
    field_simp [hspeed,hA]

end Lemniscate
