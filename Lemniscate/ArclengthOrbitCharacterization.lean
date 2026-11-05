import Lemniscate.ArclengthReparametrizationShift
import Lemniscate.OrderIsoDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Field.Periodic

/-! Oriented reparametrization of closed immersed curves is equality of
their fractional arclength parametrizations up to one compact phase. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped ContDiff

/-- Equality of oriented curves under a smooth increasing parameter
change with a smooth inverse and the prescribed period shift. -/
def OrientedCurveEquivalent (γ η : ℝ → ℂ) (P Q : ℝ) : Prop :=
  ∃ χ : ℝ ≃o ℝ,
    ContDiff ℝ ∞ (χ : ℝ → ℝ) ∧ ContDiff ℝ ∞ (χ.symm : ℝ → ℝ) ∧
      (∀ s, χ (s+Q)=χ s+P) ∧ ∀ s, γ (χ s)=η s

private theorem inverse_arclength_deck (A : ℝ ≃o ℝ) (P L : ℝ)
    (hA : ∀ s, A (s+P)=A s+L) (u : ℝ) :
    A.symm (u+L)=A.symm u+P := by
  apply A.injective
  rw [A.apply_symm_apply,hA,A.apply_symm_apply]

private theorem fractional_arclength_speed (γ : ℝ → ℂ)
    (hγ : Differentiable ℝ γ) (hreg : ∀ s, deriv γ s ≠ 0)
    (A : ℝ ≃o ℝ)
    (hAi : ∀ x, HasDerivAt (A.symm : ℝ → ℝ) (‖deriv γ (A.symm x)‖)⁻¹ x)
    (L : ℝ) (hL : 0<L) (q : ℝ) :
    ∃ v : ℂ, HasDerivAt (fun u => γ (A.symm (L*u))) v q ∧ ‖v‖=L := by
  let x := A.symm (L*q)
  let d : ℝ := ‖deriv γ x‖⁻¹*L
  have hi : HasDerivAt (fun u : ℝ => A.symm (L*u)) d q := by
    simpa only [x,d,id_eq,mul_one,Function.comp_def] using!
      (hAi (L*q)).comp q ((hasDerivAt_id q).const_mul L)
  have hc := (hγ x).hasDerivAt.scomp q hi
  have hn : 0<‖deriv γ x‖ := norm_pos_iff.mpr (hreg x)
  have hd : 0<d := mul_pos (inv_pos.mpr hn) hL
  refine ⟨d • deriv γ x,hc,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd]
  dsimp only [d]
  field_simp [ne_of_gt hn] <;> ring

private theorem phase_equality_lengths
    (γ η : ℝ → ℂ) (hγ : Differentiable ℝ γ) (hη : Differentiable ℝ η)
    (hγreg : ∀ s, deriv γ s ≠ 0) (hηreg : ∀ s, deriv η s ≠ 0)
    (A B : ℝ ≃o ℝ)
    (hAi : ∀ x, HasDerivAt (A.symm : ℝ → ℝ) (‖deriv γ (A.symm x)‖)⁻¹ x)
    (hBi : ∀ x, HasDerivAt (B.symm : ℝ → ℝ) (‖deriv η (B.symm x)‖)⁻¹ x)
    (L M : ℝ) (hL : 0<L) (hM : 0<M) (c : ℝ)
    (heq : ∀ q, γ (A.symm (L*(q+c)))=η (B.symm (M*q))) : L=M := by
  obtain ⟨v,hv,hnv⟩ := fractional_arclength_speed γ hγ hγreg A hAi L hL ((0:ℝ)+c)
  obtain ⟨w,hw,hnw⟩ := fractional_arclength_speed η hη hηreg B hBi M hM 0
  have hshift : HasDerivAt (fun q : ℝ => q+c) 1 0 :=
    (hasDerivAt_id 0).add_const c
  have hv' : HasDerivAt (fun q : ℝ => γ (A.symm (L*(q+c)))) v 0 := by
    simpa only [Function.comp_def,one_smul] using hv.scomp 0 hshift
  have hη' : HasDerivAt (fun q : ℝ => η (B.symm (M*q))) v 0 :=
    hv'.congr_of_eventuallyEq (Eventually.of_forall (fun q => (heq q).symm))
  have hvw : v=w := hη'.unique hw
  exact hnv.symm.trans ((congrArg norm hvw).trans hnw)

/-- Smooth oriented equivalence is exactly equality of the actual
fractional arclength curves after a phase in the compact interval [0,1].
The common length is derived from the equality, rather than assumed. -/
theorem oriented_curve_equivalent_iff_arclength_phase
    (γ η : ℝ → ℂ) (P Q : ℝ)
    (hγ : ContDiff ℝ ∞ γ) (hη : ContDiff ℝ ∞ η)
    (hγreg : ∀ s, deriv γ s ≠ 0) (hηreg : ∀ s, deriv η s ≠ 0)
    (hγper : Function.Periodic γ P)
    (A B : ℝ ≃o ℝ)
    (hAs : ContDiff ℝ ∞ (A : ℝ → ℝ)) (hAis : ContDiff ℝ ∞ (A.symm : ℝ → ℝ))
    (hBs : ContDiff ℝ ∞ (B : ℝ → ℝ)) (hBis : ContDiff ℝ ∞ (B.symm : ℝ → ℝ))
    (hA : ∀ u, HasDerivAt (A : ℝ → ℝ) ‖deriv γ u‖ u)
    (hB : ∀ s, HasDerivAt (B : ℝ → ℝ) ‖deriv η s‖ s)
    (hAi : ∀ x, HasDerivAt (A.symm : ℝ → ℝ) (‖deriv γ (A.symm x)‖)⁻¹ x)
    (hBi : ∀ x, HasDerivAt (B.symm : ℝ → ℝ) (‖deriv η (B.symm x)‖)⁻¹ x)
    (L M : ℝ) (hL : 0<L) (hM : 0<M)
    (hAdeck : ∀ u, A (u+P)=A u+L) (hBdeck : ∀ s, B (s+Q)=B s+M) :
    OrientedCurveEquivalent γ η P Q ↔
      ∃ c ∈ Icc (0:ℝ) 1, ∀ q : ℝ,
        γ (A.symm (L*(q+c)))=η (B.symm (M*q)) := by
  constructor
  · rintro ⟨χ,hχ,hχi,hχdeck,hcurve⟩
    obtain ⟨d,hlength,hshift⟩ := oriented_reparametrization_arclength_shift γ η A B χ
      (hγ.differentiable (by simp)) (hχ.differentiable (by simp))
      (order_iso_deriv_pos χ (hχ.differentiable (by simp)) (hχi.differentiable (by simp)))
      hcurve hA hB P Q L M hAdeck hBdeck hχdeck
    let G : ℝ → ℂ := fun q => γ (A.symm (L*q))
    have hGper : Function.Periodic G 1 := by
      intro q
      change γ (A.symm (L*(q+1)))=γ (A.symm (L*q))
      rw [show L*(q+1)=L*q+L by ring,inverse_arclength_deck A P L hAdeck,hγper]
    let F : ℝ → ℝ → ℂ := fun c q => G (q+c)
    have hFper : Function.Periodic F 1 := by
      intro c
      funext q
      dsimp only [F]
      rw [show q+(c+1)=(q+c)+1 by ring]
      exact hGper (q+c)
    obtain ⟨c,hc,hFc⟩ := hFper.exists_mem_Ico₀ (by norm_num : (0:ℝ)<1) (d/L)
    refine ⟨c,⟨hc.1,hc.2.le⟩,?_⟩
    intro q
    have hraw := hcurve (B.symm (M*q))
    rw [hshift,B.apply_symm_apply] at hraw
    have hs : L*(q+d/L)=M*q+d := by
      rw [← hlength]
      field_simp [ne_of_gt hL] <;> ring
    have hraw' : F (d/L) q=η (B.symm (M*q)) :=
      (congrArg (fun x : ℝ => γ (A.symm x)) hs).trans hraw
    exact (congrFun hFc q).symm.trans hraw'
  · rintro ⟨c,hc,hphase⟩
    have hlength : L=M := phase_equality_lengths γ η
      (hγ.differentiable (by simp)) (hη.differentiable (by simp)) hγreg hηreg
      A B hAi hBi L M hL hM c hphase
    let χ : ℝ ≃o ℝ := (B.trans (OrderIso.addRight (L*c))).trans A.symm
    have hχ : ContDiff ℝ ∞ (χ : ℝ → ℝ) :=
      hAis.comp (hBs.add contDiff_const)
    have hinv (s : ℝ) : χ.symm s=B.symm (A s-L*c) := by
      apply χ.injective
      rw [χ.apply_symm_apply]
      change s=A.symm (B (B.symm (A s-L*c))+L*c)
      rw [B.apply_symm_apply,sub_add_cancel,A.symm_apply_apply]
    have hχi : ContDiff ℝ ∞ (χ.symm : ℝ → ℝ) := by
      rw [show (χ.symm : ℝ → ℝ)=(fun s => B.symm (A s-L*c)) from funext hinv]
      exact hBis.comp (hAs.sub contDiff_const)
    refine ⟨χ,hχ,hχi,?_,?_⟩
    · intro s
      change A.symm (B (s+Q)+L*c)=A.symm (B s+L*c)+P
      rw [hBdeck,← hlength]
      rw [show B s+L+L*c=(B s+L*c)+L by ring,inverse_arclength_deck A P L hAdeck]
    · intro s
      have hh := hphase (B s/M)
      have hl : L*(B s/M+c)=B s+L*c := by
        rw [hlength]
        field_simp [ne_of_gt hM] <;> ring
      have hr : M*(B s/M)=B s := by field_simp [ne_of_gt hM]
      rw [hl,hr,B.symm_apply_apply] at hh
      exact hh

end Lemniscate
