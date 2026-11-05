import Lemniscate.PhysicalNormalizationRegularity
import Lemniscate.PartialSpatialDerivative

/-! The actual inverse normalization preserves smoothness of a given
curve family and supplies its actual smooth spatial velocity, including
the initial boundary of the time domain. -/
noncomputable section
namespace Lemniscate
open Set
open scoped ContDiff

/-- Normalize a smooth physical curve family by the exact physical clock
and scale. The spatial derivative is derived on the closed time domain;
neither a negative-time extension nor a separate smooth velocity is assumed. -/
theorem normalized_curve_family_regularity
    (a : ℝ) (ha : 0<a) (ρ : ℝ → ℝ)
    (hρ : ∀ t : ℝ, 0≤t → ρ t=(a^4+30*t)^(1/4:ℝ))
    (Y : ℝ × ℝ → ℂ)
    (hY : ContDiffOn ℝ ∞ Y ((Ici (0:ℝ)) ×ˢ (univ : Set ℝ)))
    (p : ℂ) :
    let X : ℝ × ℝ → ℂ := fun z =>
      (ρ (physicalTime a z.1):ℂ)⁻¹*(Y (physicalTime a z.1,z.2)-p)
    ContDiffOn ℝ ∞ X ((Ici (0:ℝ)) ×ˢ (univ : Set ℝ)) ∧
      ∃ V : ℝ × ℝ → ℂ,
        ContDiffOn ℝ ∞ V ((Ici (0:ℝ)) ×ˢ (univ : Set ℝ)) ∧
        ∀ σ : ℝ, 0≤σ → ∀ s : ℝ,
          HasDerivAt (fun u => X (σ,u)) (V (σ,s)) s := by
  dsimp only
  let S := (Ici (0:ℝ)) ×ˢ (univ : Set ℝ)
  let X : ℝ × ℝ → ℂ := fun z =>
    (ρ (physicalTime a z.1):ℂ)⁻¹*(Y (physicalTime a z.1,z.2)-p)
  have hreg := physical_normalization_regularity a ha ρ hρ
  have hInv := physical_time_inverse a ha
  have hT : ContDiff ℝ ∞ (fun z : ℝ × ℝ => physicalTime a z.1) :=
    hreg.1.comp contDiff_fst
  have hTmap : MapsTo (fun z : ℝ × ℝ => physicalTime a z.1) S (Ici (0:ℝ)) :=
    fun z hz => (hInv.2.1 z.1).2.2.1 hz.1
  have hR : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => ρ (physicalTime a z.1)) S :=
    hreg.2.2.comp hT.contDiffOn hTmap
  have hRpos (z : ℝ × ℝ) (hz : z∈S) : 0<ρ (physicalTime a z.1) := by
    rw [hρ _ (hTmap hz)]
    exact Real.rpow_pos_of_pos
      (add_pos_of_pos_of_nonneg (pow_pos ha 4)
        (mul_nonneg (by norm_num) (hTmap hz))) _
  have hRc : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (ρ (physicalTime a z.1):ℂ)) S :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ))).comp_contDiffOn hR
  have hRi : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (ρ (physicalTime a z.1):ℂ)⁻¹) S :=
    hRc.inv (fun z hz => Complex.ofReal_ne_zero.mpr (hRpos z hz).ne')
  have hInput : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (physicalTime a z.1,z.2)) :=
    hT.prodMk contDiff_snd
  have hYc : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y (physicalTime a z.1,z.2)) S :=
    hY.comp hInput.contDiffOn (fun z hz => ⟨hTmap hz,mem_univ z.2⟩)
  have hX : ContDiffOn ℝ ∞ X S := hRi.mul (hYc.sub contDiffOn_const)
  have hSpatial := spatial_derivative_within_smooth
    (Ici (0:ℝ)) (univ : Set ℝ) (uniqueDiffOn_Ici 0) isOpen_univ X hX
  let V : ℝ × ℝ → ℂ := fun z =>
    spatialDerivativeWithin (Ici (0:ℝ)) (univ : Set ℝ) X z 1
  have hV : ContDiffOn ℝ ∞ V S := by
    simpa only [V] using hSpatial.1.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (1:ℝ)) S)
  refine ⟨hX,V,hV,?_⟩
  intro σ hσ s
  exact (hSpatial.2 σ hσ s (mem_univ s)).hasDerivAt

end Lemniscate
