import Lemniscate.NormalGraphElasticForce

/-! The actual normal-graph flow and its quasilinear form.

The highest derivative has coefficient -g^(-4), and the remaining jet expression
depends on height derivatives only up to order three. The pointwise directional
derivative below is separate from an H4-to-L2 Frechet statement.
-/
noncomputable section
namespace Lemniscate
open Complex Filter
open scoped ComplexConjugate Topology

def normalGraphFlowRHS (β n : ℝ → ℂ) (k h : ℝ → ℝ) (c s : ℝ) : ℝ :=
  let γ := normalGraphCurve β n h;
  -(‖deriv γ s‖ / (1-k s*h s)*
    (arclengthDerivative γ (arclengthDerivative γ (planarSignedCurvature γ)) s+
      (1/2:ℝ)*(planarSignedCurvature γ s)^3+c*planarNormalSupport γ s))

private theorem normal_graph_flow_eq_jet
    (β t n : ℝ → ℂ) (k ks kss ksss h h₁ h₂ h₃ h₄ : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t ((k s:ℂ)*n s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s)
    (hks : ∀ s, HasDerivAt ks (kss s) s)
    (hkss : ∀ s, HasDerivAt kss (ksss s) s)
    (hh : ∀ s, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s, HasDerivAt h₁ (h₂ s) s)
    (hh₂ : ∀ s, HasDerivAt h₂ (h₃ s) s)
    (hh₃ : ∀ s, HasDerivAt h₃ (h₄ s) s)
    (htunit : ∀ s, ‖t s‖ = 1) (hnormal : ∀ s, n s = I*t s)
    (hregular : ∀ s, 0 < 1-k s*h s) (c s : ℝ) :
    let K : NormalGraphBackgroundJet :=
      ⟨k s,ks s,kss s,ksss s,(conj (t s)*β s).im,(conj (t s)*β s).re⟩
    let J : NormalGraphHeightJet := ⟨h s,h₁ s,h₂ s,h₃ s,h₄ s⟩
    normalGraphFlowRHS β n k h c s = normalGraphJetFlow K c J := by
  have hforce := normal_graph_elastic_force β t n k ks kss ksss h h₁ h₂ h₃ h₄
    hβ ht hn hk hks hkss hh hh₁ hh₂ hh₃ htunit hnormal hregular c s
  have hspeed := (normal_graph_geometry β t n k ks h h₁ h₂
    hβ ht hn hk hh hh₁ htunit hnormal s).2.2.1
  dsimp only [normalGraphFlowRHS]
  rw [hforce,hspeed]
  rfl

/-- The actual geometric flow is quasilinear of order four. The second term
contains no fourth derivative of the graph height. -/
theorem normal_graph_flow_quasilinear
    (β t n : ℝ → ℂ) (k ks kss ksss h h₁ h₂ h₃ h₄ : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t ((k s:ℂ)*n s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s)
    (hks : ∀ s, HasDerivAt ks (kss s) s)
    (hkss : ∀ s, HasDerivAt kss (ksss s) s)
    (hh : ∀ s, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s, HasDerivAt h₁ (h₂ s) s)
    (hh₂ : ∀ s, HasDerivAt h₂ (h₃ s) s)
    (hh₃ : ∀ s, HasDerivAt h₃ (h₄ s) s)
    (htunit : ∀ s, ‖t s‖ = 1) (hnormal : ∀ s, n s = I*t s)
    (hregular : ∀ s, 0 < 1-k s*h s) (c s : ℝ) :
    let K : NormalGraphBackgroundJet :=
      ⟨k s,ks s,kss s,ksss s,(conj (t s)*β s).im,(conj (t s)*β s).re⟩
    normalGraphFlowRHS β n k h c s =
      -(((1-k s*h s)^2+(h₁ s)^2)^2)⁻¹*h₄ s+
        normalGraphJetFlow K c ⟨h s,h₁ s,h₂ s,h₃ s,0⟩ := by
  let K : NormalGraphBackgroundJet :=
    ⟨k s,ks s,kss s,ksss s,(conj (t s)*β s).im,(conj (t s)*β s).re⟩
  let J : NormalGraphHeightJet := ⟨h s,h₁ s,h₂ s,h₃ s,h₄ s⟩
  have heq : normalGraphFlowRHS β n k h c s = normalGraphJetFlow K c J :=
    normal_graph_flow_eq_jet β t n k ks kss ksss h h₁ h₂ h₃ h₄
      hβ ht hn hk hks hkss hh hh₁ hh₂ hh₃ htunit hnormal hregular c s
  rw [heq]
  exact normal_graph_jet_quasilinear K c J (hregular s)

private theorem normal_graph_small_amplitude_regular
    (k f : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ s, |k s*f s| ≤ C) (ε : ℝ) (hε : |ε| < 1/(C+1)) :
    ∀ s, 0 < 1-k s*(ε*f s) := by
  have hC1 : 0 < C+1 := by linarith
  have hεprod : |ε| * (C+1) < 1 := (lt_div_iff₀ hC1).mp hε
  have hεC : |ε| * C < 1 := by nlinarith only [hεprod,abs_nonneg ε]
  intro s
  have hterm : k s*(ε*f s) < 1 := by
    calc
      k s*(ε*f s) = ε*(k s*f s) := by ring
      _ ≤ |ε*(k s*f s)| := le_abs_self _
      _ = |ε| * |k s*f s| := abs_mul _ _
      _ ≤ |ε| * C := mul_le_mul_of_nonneg_left (hb s) (abs_nonneg ε)
      _ < 1 := hεC
  linarith

theorem normal_graph_flow_variation
    (β t n : ℝ → ℂ) (k ks kss ksss f f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t ((k s:ℂ)*n s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s)
    (hks : ∀ s, HasDerivAt ks (kss s) s)
    (hkss : ∀ s, HasDerivAt kss (ksss s) s)
    (hf : ∀ s, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s, HasDerivAt f₁ (f₂ s) s)
    (hf₂ : ∀ s, HasDerivAt f₂ (f₃ s) s)
    (hf₃ : ∀ s, HasDerivAt f₃ (f₄ s) s)
    (htunit : ∀ s, ‖t s‖ = 1) (hnormal : ∀ s, n s = I*t s)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ s, |k s*f s| ≤ C) (c s : ℝ) :
    HasDerivAt (fun ε : ℝ => normalGraphFlowRHS β n k (fun u => ε*f u) c s)
      (-f₄ s-(5/2:ℝ)*(k s)^2*f₂ s-
        (5*k s*ks s-c*(conj (t s)*β s).re)*f₁ s-
        (3*(ks s)^2+4*k s*kss s+(3/2:ℝ)*(k s)^4+c)*f s) 0 := by
  obtain ⟨C,hC,hb⟩ := hbound
  let K : NormalGraphBackgroundJet :=
    ⟨k s,ks s,kss s,ksss s,(conj (t s)*β s).im,(conj (t s)*β s).re⟩
  let F : NormalGraphHeightJet := ⟨f s,f₁ s,f₂ s,f₃ s,f₄ s⟩
  have hradius : 0 < 1/(C+1) := one_div_pos.mpr (by linarith : 0 < C+1)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, |ε| < 1/(C+1) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hradius] with ε hε
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hε
  have heq :
      (fun ε : ℝ => normalGraphFlowRHS β n k (fun u => ε*f u) c s) =ᶠ[𝓝 0]
      (fun ε : ℝ => normalGraphJetFlow K c (normalGraphScaleHeight ε F)) := by
    refine hsmall.mono ?_
    intro ε hε
    have hregular : ∀ u, 0 < 1-k u*(ε*f u) :=
      normal_graph_small_amplitude_regular k f C hC hb ε hε
    have hd₀ (u : ℝ) : HasDerivAt (fun v => ε*f v) (ε*f₁ u) u :=
      (hf u).const_mul ε
    have hd₁ (u : ℝ) : HasDerivAt (fun v => ε*f₁ v) (ε*f₂ u) u :=
      (hf₁ u).const_mul ε
    have hd₂ (u : ℝ) : HasDerivAt (fun v => ε*f₂ v) (ε*f₃ u) u :=
      (hf₂ u).const_mul ε
    have hd₃ (u : ℝ) : HasDerivAt (fun v => ε*f₃ v) (ε*f₄ u) u :=
      (hf₃ u).const_mul ε
    exact normal_graph_flow_eq_jet β t n k ks kss ksss
      (fun u => ε*f u) (fun u => ε*f₁ u) (fun u => ε*f₂ u)
      (fun u => ε*f₃ u) (fun u => ε*f₄ u)
      hβ ht hn hk hks hkss hd₀ hd₁ hd₂ hd₃ htunit hnormal hregular c s
  simpa only [K,F] using
    (normal_graph_jet_flow_hasDerivAt K c F).congr_of_eventuallyEq heq

end Lemniscate
