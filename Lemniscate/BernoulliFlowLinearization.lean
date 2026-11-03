import Lemniscate.BernoulliArclengthFrame
import Lemniscate.NormalGraphFlowVariation

/-! The actual normal-graph flow at the Bernoulli lemniscate has the
linearization used in the spectral theorem. Spatial derivatives of f are in
x = sqrt(2) * s, whereas the geometric flow is evaluated in physical arclength s.
All Frenet and support identities are derived from the actual curve.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

theorem bernoulli_flow_linearization (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (f f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hf₃ : ∀ x, HasDerivAt f₃ (f₄ x) x)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ x, |f x| ≤ C) (x : ℝ) :
    let φ : ℝ → ℝ := fun s => e.symm (Real.sqrt 2*s)
    let Γ := bernoulliCurve ∘ φ
    let n : ℝ → ℂ := fun s =>
      I*(bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ))
    let q := bernoulliProfileQ ∘ e.symm
    let p := bernoulliProfileP ∘ e.symm
    HasDerivAt (fun ε : ℝ => normalGraphFlowRHS Γ n
        (fun s => 3*q (Real.sqrt 2*s))
        (fun s => ε*f (Real.sqrt 2*s)) (15/2) (x/Real.sqrt 2))
      (-4*f₄ x-45*(q x)^2*f₂ x-75*q x*p x*f₁ x-
        (69/2:ℝ)*f x-(45/2:ℝ)*(q x)^4*f x) 0 := by
  let d : ℝ → ℝ := fun s => Real.sqrt 2*s
  let φ : ℝ → ℝ := fun s => e.symm (d s)
  let Γ := bernoulliCurve ∘ φ
  let t : ℝ → ℂ := fun s =>
    bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  let n : ℝ → ℂ := fun s => I*t s
  let q := bernoulliProfileQ ∘ e.symm
  let p := bernoulliProfileP ∘ e.symm
  let k : ℝ → ℝ := fun s => 3*q (d s)
  let ks : ℝ → ℝ := fun s => 3*Real.sqrt 2*p (d s)
  let kss : ℝ → ℝ := fun s => -6*(q (d s))^3
  let ksss : ℝ → ℝ := fun s => -18*Real.sqrt 2*(q (d s))^2*p (d s)
  let h : ℝ → ℝ := fun s => f (d s)
  let h₁ : ℝ → ℝ := fun s => Real.sqrt 2*f₁ (d s)
  let h₂ : ℝ → ℝ := fun s => 2*f₂ (d s)
  let h₃ : ℝ → ℝ := fun s => 2*Real.sqrt 2*f₃ (d s)
  let h₄ : ℝ → ℝ := fun s => 4*f₄ (d s)
  have hframe := bernoulli_arclength_frame e he
  have henergy (s : ℝ) : 2*(p (d s))^2+(q (d s))^4 = 1 :=
    (hframe s).2.2.2.2.2.2.2.2.2
  have hposition (s : ℝ) : (conj (t s)*Γ s).re =
      Real.sqrt 2*q (d s)*p (d s) := by
    have hp := congrArg Complex.re ((hframe s).2.2.2.2.2.2.2.2.1)
    simpa only [t,Γ,φ,q,p,d,Function.comp_def,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_zero,add_zero] using hp
  have hd (s : ℝ) : HasDerivAt d (Real.sqrt 2) s := by
    simpa only [d,id_eq,mul_one] using (hasDerivAt_id s).const_mul (Real.sqrt 2)
  have hh (s : ℝ) : HasDerivAt h (h₁ s) s := by
    convert! (hf (d s)).comp s (hd s) using 1
    dsimp only [h₁]
    ring
  have hh₁ (s : ℝ) : HasDerivAt h₁ (h₂ s) s := by
    convert! ((hf₁ (d s)).comp s (hd s)).const_mul (Real.sqrt 2) using 1
    dsimp only [h₂]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring
  have hh₂ (s : ℝ) : HasDerivAt h₂ (h₃ s) s := by
    convert! ((hf₂ (d s)).comp s (hd s)).const_mul 2 using 1
    dsimp only [h₃]
    ring
  have hh₃ (s : ℝ) : HasDerivAt h₃ (h₄ s) s := by
    convert! ((hf₃ (d s)).comp s (hd s)).const_mul (2*Real.sqrt 2) using 1
    dsimp only [h₄]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring
  have hkh : ∃ C : ℝ, 0 < C ∧ ∀ s, |k s*h s| ≤ C := by
    obtain ⟨C,hC,hfC⟩ := hbound
    refine ⟨3*C,mul_pos (by norm_num) hC,?_⟩
    intro s
    have hq4 : (q (d s))^4 ≤ 1 := by
      nlinarith only [henergy s,sq_nonneg (p (d s))]
    have hq2 : (q (d s))^2 ≤ 1 :=
      (sq_le_one_iff₀ (sq_nonneg (q (d s)))).mp (by
        nlinarith only [hq4])
    have hqabs : |q (d s)| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp hq2
    have hkabs : |k s| ≤ 3 := by
      dsimp only [k]
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)]
      nlinarith only [hqabs]
    rw [abs_mul]
    exact mul_le_mul hkabs (hfC (d s)) (abs_nonneg _) (by norm_num)
  have hvar := normal_graph_flow_variation Γ t n k ks kss ksss h h₁ h₂ h₃ h₄
    (fun s => (hframe s).1)
    (fun s => (hframe s).2.2.1)
    (fun s => (hframe s).2.2.2.1)
    (fun s => (hframe s).2.2.2.2.1)
    (fun s => (hframe s).2.2.2.2.2.1)
    (fun s => (hframe s).2.2.2.2.2.2.1)
    hh hh₁ hh₂ hh₃ (fun s => (hframe s).2.1) (fun _ => rfl) hkh
    (15/2) (x/Real.sqrt 2)
  rw [hposition] at hvar
  have hroot : Real.sqrt (2:ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hscale : Real.sqrt 2*(x/Real.sqrt 2) = x := by
    field_simp [hroot] <;> ring
  have hscaled := bernoulli_normal_graph_linearization_scaling (q x) (p x)
    (f x) (f₁ x) (f₂ x) (f₄ x) (by
      simpa only [d,hscale] using henergy (x/Real.sqrt 2))
  simp only [k,ks,kss,h,h₁,h₂,h₄,d,hscale] at hvar
  rw [hscaled] at hvar
  exact hvar

end Lemniscate
