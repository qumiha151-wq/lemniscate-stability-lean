import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The residual estimate for a selected normal projection gives its
actual continuous trace at an initially aligned graph. This uses only
joint continuity of the curve and the reference frame. -/
noncomputable section
namespace Lemniscate
open Complex Filter
open scoped Topology ComplexConjugate

/-- A selected normal projection which is continuous off the initial
parameter is jointly continuous across that parameter. The normal height
is recovered from the actual graph identity, so no separate continuity
assumption on the selected height is needed. -/
theorem parametric_normal_projection_trace_continuous
    {X : Type*} [TopologicalSpace X] (p₀ : X)
    (Γ : X × ℝ → ℂ) (hΓ : Continuous Γ)
    (β T : ℝ → ℂ) (hβ : Continuous β) (hT : Continuous T)
    (hunit : ∀ s, ‖T s‖=1) (h₀ : ℝ → ℝ)
    (hinitial : ∀ s, Γ (p₀,s)=β s+I*(h₀ s:ℂ)*T s)
    (χ H : X × ℝ → ℝ)
    (hχinitial : ∀ s, χ (p₀,s)=s)
    (hχoff : ∀ z : X × ℝ, z.1 ≠ p₀ → ContinuousAt χ z)
    (hresidual : ∀ p : X, p ≠ p₀ → ∀ s : ℝ,
      |χ (p,s)-s|≤2*|(conj (T s)*(Γ (p,s)-β s)).re|)
    (hgraph : ∀ p : X, ∀ s : ℝ,
      Γ (p,χ (p,s))=β s+I*(H (p,s):ℂ)*T s) :
    Continuous χ ∧ Continuous H := by
  have hself (s : ℝ) : conj (T s)*T s=1 := by rw [Complex.conj_mul',hunit]; simp
  have hpair (s a : ℝ) : conj (T s)*(I*(a:ℂ)*T s)=I*(a:ℂ) := by
    calc
      _ = (I*(a:ℂ))*(conj (T s)*T s) := by ring
      _ = _ := by rw [hself,mul_one]
  let R : X × ℝ → ℝ := fun z => 2*|(conj (T z.2)*(Γ z-β z.2)).re|
  have hC : Continuous (fun z : X × ℝ => conj (T z.2)*(Γ z-β z.2)) :=
    (Complex.conjCLE.continuous.comp (hT.comp continuous_snd)).mul
      (hΓ.sub (hβ.comp continuous_snd))
  have hR : Continuous R :=
    (continuous_const : Continuous (fun _ : X × ℝ => (2:ℝ))).mul
      ((Complex.reCLM.continuous.comp hC).abs)
  have hRzero (s : ℝ) : R (p₀,s)=0 := by
    dsimp only [R]
    rw [hinitial,add_sub_cancel_left,hpair]
    simp [Complex.mul_re]
  have hbound (z : X × ℝ) : ‖χ z-z.2‖≤R z := by
    by_cases hp : z.1=p₀
    · have hz : χ z-z.2=0 := by
        change χ (z.1,z.2)-z.2=0
        rw [hp,hχinitial,sub_self]
      rw [hz,norm_zero]
      exact mul_nonneg (by norm_num) (abs_nonneg _)
    · simpa only [Real.norm_eq_abs,R] using hresidual z.1 hp z.2
  have hχbase (s : ℝ) : ContinuousAt χ (p₀,s) := by
    have hr : Tendsto R (𝓝 (p₀,s)) (𝓝 (0:ℝ)) := by
      simpa only [hRzero] using hR.tendsto (p₀,s)
    have hd : Tendsto (fun z : X × ℝ => χ z-z.2) (𝓝 (p₀,s)) (𝓝 (0:ℝ)) :=
      squeeze_zero_norm hbound hr
    have hs : Tendsto (fun z : X × ℝ => z.2) (𝓝 (p₀,s)) (𝓝 s) :=
      continuous_snd.tendsto (p₀,s)
    change Tendsto χ (𝓝 (p₀,s)) (𝓝 (χ (p₀,s)))
    rw [hχinitial]
    simpa only [Pi.add_apply,sub_add_cancel,zero_add] using hd.add hs
  have hχ : Continuous χ := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨p,s⟩
    by_cases hp : p=p₀
    · subst p
      exact hχbase s
    · exact hχoff (p,s) hp
  have hheight (p : X) (s : ℝ) :
      H (p,s)=(conj (T s)*(Γ (p,χ (p,s))-β s)).im := by
    rw [hgraph,add_sub_cancel_left,hpair]
    simp [Complex.mul_im]
  have hinput : Continuous (fun z : X × ℝ => (z.1,χ z)) := continuous_fst.prodMk hχ
  have hcomposed : Continuous (fun z : X × ℝ => conj (T z.2)*(Γ (z.1,χ z)-β z.2)) :=
    (Complex.conjCLE.continuous.comp (hT.comp continuous_snd)).mul
      ((hΓ.comp hinput).sub (hβ.comp continuous_snd))
  have hH : Continuous H := by
    have heq : H=(fun z : X × ℝ => (conj (T z.2)*(Γ (z.1,χ z)-β z.2)).im) :=
      funext (fun z => hheight z.1 z.2)
    rw [heq]
    exact Complex.imCLM.continuous.comp hcomposed
  exact ⟨hχ,hH⟩

end Lemniscate
