import Lemniscate.ArclengthOrbitCharacterization
import Lemniscate.PeriodicParameterChange

/-! The actual projection coordinates induce a smooth oriented parameter
change between the original closed curve and its physical normal graph. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ContDiff

/-- Rescale the actual auxiliary projection and compose it with the fixed
original parameter change. The smooth inverse is constructed from the
positive spatial derivative and the existing displacement bound. -/
theorem normal_graph_oriented_parameter_change
    (S ℓ P b R : ℝ) (hℓ : 0<ℓ) (hb : 0<b) (hS : S=b*ℓ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hdeck : ∀ x, χ (x+S)=χ x+S)
    (hpositive : ∀ x, 0<deriv χ x) (hbound : ∀ x, |χ x-x|≤R)
    (χ₀ : ℝ ≃o ℝ)
    (hχ₀ : ContDiff ℝ ∞ (χ₀ : ℝ → ℝ))
    (hχ₀inv : ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ))
    (hχ₀deck : ∀ s, χ₀ (s+ℓ)=χ₀ s+P)
    (γ η : ℝ → ℂ) (hgraph : ∀ s, γ (χ₀ (χ (b*s)/b))=η s) :
    OrientedCurveEquivalent γ η P ℓ := by
  have hSpos : 0<S := by rw [hS]; exact mul_pos hb hℓ
  obtain ⟨E,hE,hEs,hEis,hEdeck,_⟩ :=
    periodic_parameter_change S hSpos χ R hχ hdeck hpositive hbound
  let B : ℝ ≃o ℝ := OrderIso.mulLeft₀ b hb
  let F : ℝ ≃o ℝ := ((B.trans E).trans B.symm).trans χ₀
  have hF (s : ℝ) : F s=χ₀ (E (b*s)/b) := by
    change χ₀ (b⁻¹*E (b*s))=χ₀ (E (b*s)/b)
    rw [div_eq_mul_inv,mul_comm b⁻¹]
  have hFi (u : ℝ) : F.symm u=E.symm (b*χ₀.symm u)/b := by
    change b⁻¹*E.symm (b*χ₀.symm u)=E.symm (b*χ₀.symm u)/b
    rw [div_eq_mul_inv,mul_comm b⁻¹]
  have hFs : ContDiff ℝ ∞ (F : ℝ → ℝ) := by
    have heq : (F : ℝ → ℝ)=(fun s => χ₀ (E (b*s)/b)) := funext hF
    rw [heq]
    exact hχ₀.comp ((hEs.comp (contDiff_const.mul contDiff_id)).div_const b)
  have hFis : ContDiff ℝ ∞ (F.symm : ℝ → ℝ) := by
    have heq : (F.symm : ℝ → ℝ)=(fun u => E.symm (b*χ₀.symm u)/b) := funext hFi
    rw [heq]
    exact (hEis.comp (contDiff_const.mul hχ₀inv)).div_const b
  refine ⟨F,hFs,hFis,?_,?_⟩
  · intro s
    rw [hF,hF]
    have harg : b*(s+ℓ)=b*s+S := by rw [hS]; ring
    rw [harg,hEdeck,add_div,hS,mul_div_cancel_left₀ ℓ hb.ne']
    exact hχ₀deck (E (b*s)/b)
  · intro s
    rw [hF,hE]
    exact hgraph s

end Lemniscate
