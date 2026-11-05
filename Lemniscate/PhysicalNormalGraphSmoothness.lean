import Lemniscate.PhysicalNormalizationRegularity

/-! Smoothness of the actual physical normal graph, including the initial
boundary, is preserved by the exact clock, scale and phase reconstruction. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff

/-- A jointly smooth normalized height and smooth rotation angle produce
a jointly smooth physical normal graph on the closed physical time axis. -/
theorem physical_normal_graph_smoothness
    (a : ℝ) (ha : 0<a) (ρ : ℝ → ℝ)
    (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ))
    (α : ℝ) (p₀ : ℂ) (β ν : ℝ → ℂ)
    (hβ : ContDiff ℝ ∞ β) (hν : ContDiff ℝ ∞ ν)
    (H : ℝ → ℝ → ℝ) (θ : ℝ → ℝ)
    (hH : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => H z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hθ : ContDiffOn ℝ ∞ θ (Ici (0:ℝ)))
    (P : ℝ) (hβper : Function.Periodic β P) (hνper : Function.Periodic ν P)
    (hHper : ∀ σ : ℝ,0≤σ → Function.Periodic (H σ) P)
    (Core : ℝ → ℝ → ℂ)
    (hvalue : ∀ t : ℝ,0≤t → ∀ s : ℝ,
      Core t s=p₀+(ρ t:ℂ)*
        (Complex.exp (((α+θ (normalizedTime a t)):ℂ)*I)*
          (β s+(H (normalizedTime a t) s:ℂ)*ν s))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Core z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
      ∀ t : ℝ,0≤t → Function.Periodic (Core t) P := by
  let A : Set (ℝ × ℝ) := Ici (0:ℝ) ×ˢ (univ : Set ℝ)
  have hr := physical_normalization_regularity a ha ρ hρ
  have hnonneg (t : ℝ) (ht : 0≤t) : 0≤normalizedTime a t := by
    obtain ⟨r,hr⟩ := physical_normalization a ha
    exact (hr.2.2.1 t ht).2.2.1
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => normalizedTime a z.1) A :=
    hr.2.1.comp contDiffOn_fst (fun z hz => hz.1)
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (ρ z.1:ℂ)) A :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hr.2.2.comp contDiffOn_fst (fun z hz => hz.1))
  have hclock : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => (normalizedTime a z.1,z.2)) A := hc.prodMk contDiffOn_snd
  have hmaps : MapsTo (fun z : ℝ × ℝ => (normalizedTime a z.1,z.2)) A A :=
    fun z hz => ⟨hnonneg z.1 hz.1,mem_univ z.2⟩
  have hh : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (H (normalizedTime a z.1) z.2:ℂ)) A :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hH.comp hclock hmaps)
  have ht : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => θ (normalizedTime a z.1)) A :=
    hθ.comp hc (fun z hz => hnonneg z.1 hz.1)
  have hangle : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => ((α+θ (normalizedTime a z.1):ℝ):ℂ)) A :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.add ht)
  have he : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
      Complex.exp (((α+θ (normalizedTime a z.1)):ℂ)*I)) A :=
    by
      have hm : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
          ((α+θ (normalizedTime a z.1):ℝ):ℂ)*I) A :=
        hangle.mul (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (I:ℂ)) A)
      simpa only [Complex.ofReal_add] using! hm.cexp
  have hb : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => β z.2) A :=
    hβ.contDiffOn.comp contDiffOn_snd (mapsTo_univ _ _)
  have hn : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => ν z.2) A :=
    hν.contDiffOn.comp contDiffOn_snd (mapsTo_univ _ _)
  have hraw : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
      p₀+(ρ z.1:ℂ)*(Complex.exp (((α+θ (normalizedTime a z.1)):ℂ)*I)*
        (β z.2+(H (normalizedTime a z.1) z.2:ℂ)*ν z.2))) A :=
    contDiffOn_const.add (hs.mul (he.mul (hb.add (hh.mul hn))))
  refine ⟨hraw.congr (fun z hz => hvalue z.1 hz.1 z.2),?_⟩
  intro t ht s
  rw [hvalue t ht (s+P),hvalue t ht s,hβper s,hνper s,
    hHper (normalizedTime a t) (hnonneg t ht) s]

end Lemniscate
