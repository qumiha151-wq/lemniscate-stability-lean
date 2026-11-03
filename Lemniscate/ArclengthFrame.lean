import Lemniscate.BernoulliExpander
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv

/-! The actual Frenet frame obtained by an orientation-preserving arclength
reparametrization. The curvature and support are the geometric definitions. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ComplexConjugate

private theorem complex_speed_deriv {v : ℝ → ℂ} {a : ℂ} {u : ℝ}
    (hv : HasDerivAt v a u) (h0 : v u ≠ 0) :
    HasDerivAt (fun y : ℝ => ‖v y‖) ((conj (v u)*a).re/‖v u‖) u := by
  have hr : HasDerivAt (fun y : ℝ => (v y).re) a.re u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hv
  have hi : HasDerivAt (fun y : ℝ => (v y).im) a.im u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hv
  have hsq : HasDerivAt (fun y : ℝ => ‖v y‖^2) (2*(conj (v u)*a).re) u := by
    convert! (hr.pow 2).add (hi.pow 2) using 1
    · funext y
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp only [Pi.add_apply,Pi.pow_apply]
      ring
    · simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
      ring
  have hn0 : ‖v u‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hsqrt := hsq.sqrt (pow_ne_zero 2 hn0)
  convert! hsqrt using 1
  · funext y
    rw [Real.sqrt_sq (norm_nonneg (v y))]
  · rw [Real.sqrt_sq (norm_nonneg (v u))]
    field_simp [hn0] <;> ring

private theorem complex_acceleration_normal (v a : ℂ) :
    a*(‖v‖:ℂ)^2-v*((conj v*a).re:ℂ) = I*v*((conj v*a).im:ℂ) := by
  rw [← Complex.ofReal_pow,Complex.sq_norm,Complex.normSq_apply]
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,
    Complex.I_re,Complex.I_im] <;> ring

private theorem normalized_acceleration_formula (v a : ℂ) (h0 : v ≠ 0) :
    ((a/(‖v‖:ℂ))*(‖v‖:ℂ)-v*(((conj v*a).re/‖v‖*(1/‖v‖):ℝ):ℂ))/(‖v‖:ℂ)^2 =
      (((conj v*a).im/‖v‖^3:ℝ):ℂ)*(I*(v/(‖v‖:ℂ))) := by
  have hn0 : (‖v‖:ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h0)
  calc
    _ = (a*(‖v‖:ℂ)^2-v*((conj v*a).re:ℂ))/(‖v‖:ℂ)^4 := by
      push_cast
      field_simp [hn0]
    _ = (I*v*((conj v*a).im:ℂ))/(‖v‖:ℂ)^4 := by
      rw [complex_acceleration_normal]
    _ = _ := by
      push_cast
      field_simp [hn0]

theorem arclength_frenet_frame (β v a : ℝ → ℂ) (φ : ℝ → ℝ)
    (hβ : ∀ u, HasDerivAt β (v u) u)
    (hv : ∀ u, HasDerivAt v (a u) u)
    (hφ : ∀ s, HasDerivAt φ (1/‖v (φ s)‖) s)
    (hreg : ∀ s, v (φ s) ≠ 0) :
    let Γ := β ∘ φ
    let t : ℝ → ℂ := fun s => v (φ s)/(‖v (φ s)‖:ℂ)
    let n : ℝ → ℂ := fun s => I*t s
    let k : ℝ → ℝ := fun s => planarSignedCurvature β (φ s)
    (∀ s, HasDerivAt Γ (t s) s) ∧
    (∀ s, ‖t s‖ = 1) ∧
    (∀ s, HasDerivAt t ((k s:ℂ)*n s) s) ∧
    (∀ s, HasDerivAt n (-(k s:ℂ)*t s) s) ∧
    (∀ s, planarSignedCurvature Γ s = k s) ∧
    (∀ s, planarNormalSupport Γ s = planarNormalSupport β (φ s)) := by
  let Γ := β ∘ φ
  let t : ℝ → ℂ := fun s => v (φ s)/(‖v (φ s)‖:ℂ)
  let n : ℝ → ℂ := fun s => I*t s
  let k : ℝ → ℝ := fun s => planarSignedCurvature β (φ s)
  have hdβ : deriv β = v := funext fun u => (hβ u).deriv
  have hdv : deriv v = a := funext fun u => (hv u).deriv
  have hk (s : ℝ) : k s = (conj (v (φ s))*a (φ s)).im/‖v (φ s)‖^3 := by
    dsimp only [k,planarSignedCurvature]
    rw [hdβ,hdv]
  have hΓ (s : ℝ) : HasDerivAt Γ (t s) s := by
    convert! (hβ (φ s)).scomp s (hφ s) using 1
    dsimp only [t]
    simp only [real_smul,div_eq_mul_inv,Complex.ofReal_inv]
    push_cast
    <;> ring
  have htunit (s : ℝ) : ‖t s‖ = 1 := by
    dsimp only [t]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (v (φ s)))]
    exact div_self (norm_ne_zero_iff.mpr (hreg s))
  have htangent (s : ℝ) : HasDerivAt t ((k s:ℂ)*n s) s := by
    have hV : HasDerivAt (fun y : ℝ => v (φ y))
        (a (φ s)/(‖v (φ s)‖:ℂ)) s := by
      convert! (hv (φ s)).scomp s (hφ s) using 1
      simp only [real_smul,div_eq_mul_inv,Complex.ofReal_inv]
      push_cast
      <;> ring
    have hspeed : HasDerivAt (fun y : ℝ => ‖v (φ y)‖)
        ((conj (v (φ s))*a (φ s)).re/‖v (φ s)‖*(1/‖v (φ s)‖)) s :=
      (complex_speed_deriv (hv (φ s)) (hreg s)).comp s (hφ s)
    have hn0 : (‖v (φ s)‖:ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr (hreg s))
    apply (hV.div hspeed.ofReal_comp hn0).congr_deriv
    rw [hk s]
    dsimp only [n,t]
    exact normalized_acceleration_formula (v (φ s)) (a (φ s)) (hreg s)
  have hnormal (s : ℝ) : HasDerivAt n (-(k s:ℂ)*t s) s := by
    convert! (htangent s).const_mul I using 1
    dsimp only [n]
    calc
      -(k s:ℂ)*t s = I^2*((k s:ℂ)*t s) := by rw [I_sq]; ring
      _ = I*((k s:ℂ)*(I*t s)) := by ring
  have hdΓ : deriv Γ = t := funext fun s => (hΓ s).deriv
  refine ⟨hΓ,htunit,htangent,hnormal,?_,?_⟩
  · intro s
    have hpair : conj (t s)*t s = 1 := by rw [Complex.conj_mul',htunit s]; norm_num
    change (conj (deriv Γ s)*deriv (deriv Γ) s).im/‖deriv Γ s‖^3 = k s
    rw [hdΓ,(htangent s).deriv,htunit s]
    change (conj (t s)*((k s:ℂ)*(I*t s))).im/(1:ℝ)^3 = k s
    rw [show conj (t s)*((k s:ℂ)*(I*t s)) =
      I*(k s:ℂ)*(conj (t s)*t s) by ring,hpair,mul_one]
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add,one_pow,div_one]
  · intro s
    change -(conj (Γ s)*deriv Γ s).im/‖deriv Γ s‖ =
      -(conj (β (φ s))*deriv β (φ s)).im/‖deriv β (φ s)‖
    rw [hdΓ,hdβ,htunit s]
    dsimp only [Γ,Function.comp_def,t]
    rw [← mul_div_assoc,Complex.div_ofReal_im]
    simp only [div_one,neg_div]

end Lemniscate
