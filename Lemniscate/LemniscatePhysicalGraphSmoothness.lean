import Lemniscate.BernoulliPhysicalGraphStability
import Lemniscate.PhysicalNormalGraphSmoothness

/-! The actual Sobolev height representation is composed with the physical
space and time coordinates.  No smoothness of the target curve is assumed. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff
variable (T : ℝ) [Fact (0<T)]

theorem lemniscate_physical_graph_smoothness
    (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η x₀)
    (hheight : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
      (circleSobolevH1Embedding T (circleSobolevInclusion T 1
        (D.u (Real.toNNReal z.1)))) (z.2:AddCircle T))
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hangle : ContDiffOn ℝ ∞ D.theta (Ici (0:ℝ)))
    (a : ℝ) (ha : 0<a) (α : ℝ) (ρ : ℝ → ℝ) (p₀ : ℂ)
    (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ))
    (β ν : ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hν : ContDiff ℝ ∞ ν)
    (hβper : Function.Periodic β (T/Real.sqrt 2))
    (hνper : Function.Periodic ν (T/Real.sqrt 2))
    (Core : ℝ → ℝ → ℂ)
    (hvalue : ∀ t : ℝ,0≤t → ∀ s,
      Core t s=p₀+(ρ t:ℂ)*
        (Complex.exp (((α+D.theta (normalizedTime a t)):ℂ)*I)*
          (β s+((circleSobolevH1Embedding T (circleSobolevInclusion T 1
            (D.u (Real.toNNReal (normalizedTime a t))))
              ((Real.sqrt 2*s):AddCircle T)).re:ℂ)*ν s))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Core z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
      ∀ t : ℝ,0≤t → Function.Periodic (Core t) (T/Real.sqrt 2) := by
  let H : ℝ → ℝ → ℝ := fun σ s =>
    ((circleSobolevH1Embedding T (circleSobolevInclusion T 1
      (D.u (Real.toNNReal σ)))) ((Real.sqrt 2*s):AddCircle T)).re
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.1,Real.sqrt 2*z.2)) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  have hH : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => H z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (hheight.comp hmap.contDiffOn (fun z hz => ⟨hz.1,mem_univ _⟩))
  have hper (σ : ℝ) (_hσ : 0≤σ) : Function.Periodic (H σ) (T/Real.sqrt 2) := by
    intro s
    have hscale : Real.sqrt 2*(s+T/Real.sqrt 2)=Real.sqrt 2*s+T := by
      have hsqrt : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp [hsqrt]
      <;> ring
    dsimp only [H]
    rw [hscale,AddCircle.coe_add_period]
  exact physical_normal_graph_smoothness a ha ρ hρ α p₀ β ν hβ hν H D.theta
    hH hangle (T/Real.sqrt 2) hβper hνper hper Core hvalue

end Lemniscate
