import Lemniscate.BernoulliNormalizedFlowFamilies
import Lemniscate.CurveFamilySimilarityContinuity

/-! Continuity and periodicity of the actual constructed physical graph,
obtained from its normalized H2 family and the exact physical scale. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff NNReal

variable (T : ℝ) [Fact (0<T)]

/-- The actual physical graph is periodic and continuous together with
its spatial derivative up to the initial time. No joint time smoothness
of the constructed solution is required. -/
theorem lemniscate_physical_graph_continuity
    (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η x₀)
    (a : ℝ) (ha : 0<a) (α : ℝ) (ρ : ℝ → ℝ) (p₀ : ℂ)
    (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ))
    (β ν : ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hν : ContDiff ℝ ∞ ν)
    (hβper : Function.Periodic β (T/Real.sqrt 2))
    (hνper : Function.Periodic ν (T/Real.sqrt 2))
    (Core : ℝ → ℝ → ℂ)
    (hspace : ∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Core t))
    (hregular : ∀ t : ℝ,0≤t → ∀ s,deriv (Core t) s≠0)
    (hvalue : ∀ t : ℝ,0≤t → ∀ s,
      Core t s=p₀+(ρ t:ℂ)*
        (Complex.exp (((α+D.theta (normalizedTime a t)):ℂ)*I)*
          (β s+((circleSobolevH1Embedding T (circleSobolevInclusion T 1
            (D.u (Real.toNNReal (normalizedTime a t))))
              ((Real.sqrt 2*s):AddCircle T)).re:ℂ)*ν s))) :
    (∀ t : ℝ,0≤t → Function.Periodic (Core t) (T/Real.sqrt 2)) ∧
      ContinuousOn (fun z : ℝ × ℝ => Core z.1 z.2)
        (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv (Core z.1) z.2)
        (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) := by
  have htime (σ : ℝ≥0) : 0≤physicalTime a (σ:ℝ) :=
    ((physical_time_inverse a ha).2.1 (σ:ℝ)).2.2.1 σ.property
  have hρpos (t : ℝ) (ht : 0≤t) : 0<ρ t := by
    rw [hρ t ht]
    exact Real.rpow_pos_of_pos
      (add_pos_of_pos_of_nonneg (pow_pos ha 4) (mul_nonneg (by norm_num) ht)) _
  have hclockNonnegative (t : ℝ) (ht : 0≤t) : 0≤normalizedTime a t := by
    obtain ⟨r,hr⟩ := physical_normalization a ha
    exact (hr.2.2.1 t ht).2.2.1
  have hphysical (σ : ℝ≥0) (s : ℝ) :
      Core (physicalTime a (σ:ℝ)) s=p₀+(ρ (physicalTime a (σ:ℝ)):ℂ)*
        (Complex.exp (((α+D.theta (σ:ℝ)):ℂ)*I)*
          (β s+((circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u σ))
            ((Real.sqrt 2*s):AddCircle T)).re:ℂ)*ν s)) := by
    have hh := hvalue (physicalTime a (σ:ℝ)) (htime σ) s
    simpa only [((physical_time_inverse a ha).2.1 (σ:ℝ)).1,Real.toNNReal_coe] using! hh
  let Z : ℝ≥0 × ℝ → ℂ := fun z =>
    Complex.exp (((α+D.theta (z.1:ℝ)):ℂ)*I)*
      (β z.2+((circleSobolevH1Embedding T (circleSobolevInclusion T 1 (D.u z.1))
        ((Real.sqrt 2*z.2):AddCircle T)).re:ℂ)*ν z.2)
  have hfamily := bernoulli_normal_graph_family_regularity T q p ψ τ hτ η x₀ D
    a ha α ρ p₀ (fun σ => hρpos _ (htime σ)) β ν hβ hν hβper hνper
      Core hspace hregular hphysical
  have hZ : Continuous Z := hfamily.1
  have hZv : Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => Z (z.1,s)) z.2) :=
    hfamily.2.1
  have hZs (σ : ℝ≥0) : Differentiable ℝ (fun s => Z (σ,s)) :=
    (hfamily.2.2.1 σ).differentiable (by simp)
  have hZper (σ : ℝ≥0) : Function.Periodic (fun s => Z (σ,s)) (T/Real.sqrt 2) :=
    hfamily.2.2.2.2 σ
  let clock : ℝ≥0 → ℝ≥0 := fun t => Real.toNNReal (normalizedTime a (t:ℝ))
  let scale : ℝ≥0 → ℂ := fun t => (ρ (t:ℝ):ℂ)
  have hreg := physical_normalization_regularity a ha ρ hρ
  have hclock : Continuous clock := by
    exact continuous_real_toNNReal.comp
      (hreg.2.1.continuousOn.comp_continuous continuous_subtype_val (fun t => t.property))
  have hscale : Continuous scale := by
    exact Complex.continuous_ofReal.comp
      (hreg.2.2.continuousOn.comp_continuous continuous_subtype_val (fun t => t.property))
  have hsimilarity := curve_family_similarity_continuity Z hZ hZv hZs clock hclock
    (fun _ => p₀) scale continuous_const hscale (fun s : ℝ => s) contDiff_id
  have hactual (t : ℝ) (ht : 0≤t) (s : ℝ) :
      Core t s=p₀+(ρ t:ℂ)*Z (Real.toNNReal (normalizedTime a t),s) := by
    rw [hvalue t ht s]
    simp only [Z,Real.coe_toNNReal _ (hclockNonnegative t ht)]
  let CoreN : ℝ≥0 × ℝ → ℂ := fun z => Core (z.1:ℝ) z.2
  have heq : CoreN=(fun z : ℝ≥0 × ℝ => p₀+scale z.1*Z (clock z.1,z.2)) := by
    funext z
    exact hactual (z.1:ℝ) z.1.property z.2
  have hCoreN : Continuous CoreN ∧
      Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => CoreN (z.1,s)) z.2) := by
    rw [heq]
    exact hsimilarity
  let retract : ℝ × ℝ → ℝ≥0 × ℝ := fun z => (Real.toNNReal z.1,z.2)
  have hretract : Continuous retract :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd
  refine ⟨?_,?_,?_⟩
  · intro t ht s
    rw [hactual t ht (s+T/Real.sqrt 2),hactual t ht s]
    exact congrArg (fun v : ℂ => p₀+(ρ t:ℂ)*v)
      (hZper (Real.toNNReal (normalizedTime a t)) s)
  · apply (hCoreN.1.comp hretract).continuousOn.congr
    intro z hz
    simp only [Function.comp_def,retract,CoreN,Real.coe_toNNReal z.1 hz.1]
  · apply (hCoreN.2.comp hretract).continuousOn.congr
    intro z hz
    simp only [Function.comp_def,retract,CoreN,Real.coe_toNNReal z.1 hz.1]

end Lemniscate
