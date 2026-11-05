import Lemniscate.CurveFlowTimeReparametrization
import Lemniscate.ElasticFlowNormalization

/-! The angular variation of an actual normal projection of a fixed curve.
Only the true derivatives of the selected coordinates are used. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped ContDiff Topology ComplexConjugate

/-- Rotating the reference frame of a fixed immersed curve changes the
normal height by minus the geometric rotation field. This follows from
the vanishing normal velocity of a reparametrization of the fixed curve;
no evolution equation is assumed. -/
theorem normal_graph_phase_variation
    (Γ β t n : ℝ → ℂ) (k : ℝ → ℝ)
    (χ H : ℝ → ℝ → ℝ) (θ₀ : ℝ) (b v h₁ : ℝ → ℝ)
    (hΓ : ContDiff ℝ ∞ Γ) (hΓreg : ∀ s, deriv Γ s ≠ 0)
    (hχspace : ContDiff ℝ ∞ (χ θ₀))
    (hχpos : ∀ s, 0 < deriv (χ θ₀) s)
    (hχtime : ∀ s, HasDerivAt (fun θ => χ θ s) (b s) θ₀)
    (hHtime : ∀ s, HasDerivAt (fun θ => H θ s) (v s) θ₀)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖ = 1) (hN : ∀ s, n s = I*t s)
    (hspace : ∀ s, HasDerivAt (H θ₀) (h₁ s) s)
    (hregular : ∀ s, 0 < 1-k s*H θ₀ s)
    (hgraph : ∀ᶠ θ in 𝓝 θ₀, ∀ s,
      Γ (χ θ s) = Complex.exp ((θ:ℂ)*I)*normalGraphCurve β n (H θ) s) :
    ∀ s, v s = -((conj (t s)*β s).re+
      ((conj (t s)*β s).im+H θ₀ s)*h₁ s/(1-k s*H θ₀ s)) := by
  let γ := normalGraphCurve β n (H θ₀)
  let R := Complex.exp ((θ₀:ℂ)*I)
  let V : ℝ → ℂ := fun s => R*(I*(1:ℂ)*γ s+(v s:ℂ)*n s)
  have hkin := normal_graph_rotating_velocity_equivalence β t n k H id univ
    θ₀ 1 v h₁ (fun _ => 0) hβ hn hu hN hspace
    (fun s => (hHtime s).hasDerivWithinAt)
    (hasDerivAt_id θ₀).hasDerivWithinAt hregular
  have hstationary := curve_flow_time_reparametrization (fun _ s => Γ s) χ θ₀ b
    hΓ hχspace hΓreg hχpos
    (fun s => by
      simpa only [Function.comp_def] using!
        (hΓ.differentiable (by simp) (χ θ₀ s)).comp
          (θ₀,χ θ₀ s) differentiableAt_snd) hχtime
  have hR : ‖R‖ = 1 := Complex.norm_exp_ofReal_mul_I θ₀
  have hsimilar := planar_similarity_elastic_geometry γ
    (fun s => (hkin.1 s).1) 0 R 1 (by norm_num) hR
  have hcurve : (fun s => Γ (χ θ₀ s)) = fun s => R*γ s := by
    funext s
    exact hgraph.self_of_nhds s
  intro s
  have hnormal :
      I*deriv (fun u => Γ (χ θ₀ u)) s/
          (‖deriv (fun u => Γ (χ θ₀ u)) s‖:ℂ) =
        R*(I*deriv γ s/(‖deriv γ s‖:ℂ)) := by
    rw [hcurve]
    simpa only [Complex.ofReal_one,one_mul,zero_add] using (hsimilar.1 s).2
  have hnormalzero :
      (conj (deriv (fun θ => Γ (χ θ s)) θ₀)*
        (I*deriv (fun u => Γ (χ θ₀ u)) s/
          (‖deriv (fun u => Γ (χ θ₀ u)) s‖:ℂ))).re = 0 := by
    simpa only [deriv_const,map_zero,zero_mul,Complex.zero_re] using
      (hstationary s).2.2.2.2.1
  have hevent : (fun θ => Γ (χ θ s)) =ᶠ[𝓝 θ₀]
      (fun θ => Complex.exp ((θ:ℂ)*I)*normalGraphCurve β n (H θ) s) := by
    filter_upwards [hgraph] with θ hθ
    exact hθ s
  have hvelocity : HasDerivAt (fun θ => Γ (χ θ s)) (V s) θ₀ := by
    exact (hasDerivWithinAt_univ.mp (hkin.2 s).1).congr_of_eventuallyEq hevent
  have hzero : (conj (V s)*(R*(I*deriv γ s/(‖deriv γ s‖:ℂ)))).re = -(0:ℝ) := by
    rw [hvelocity.deriv,hnormal] at hnormalzero
    simpa only [neg_zero] using hnormalzero
  have hheight := (hkin.2 s).2.mp hzero
  simp only [one_mul,mul_zero,neg_zero] at hheight
  linarith only [hheight]

end Lemniscate
