import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.Linarith

/-! The spatial ODE for normal projection has smooth coefficients on a
uniform displacement domain. Its denominator is controlled by the actual
velocity and the reference curvature, without parameter derivatives. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff ComplexConjugate

abbrev NormalProjectionState := ℝ × (ℝ × ℝ)

/-- The state is (s,χ(s)-s,h(s)); this vector field is its spatial ODE. -/
def normalProjectionVectorField {P : Type*}
    (T : ℝ → ℂ) (κ : ℝ → ℝ) (V : P × ℝ → ℂ)
    (w : P × NormalProjectionState) : NormalProjectionState :=
  let W := conj (T w.2.1)*V (w.1,w.2.1+w.2.2.1)
  let A := 1-κ w.2.1*w.2.2.2
  (1,(A/W.re-1,A/W.re*W.im))

/-- Uniform velocity proximity and a reference curvature bound make the
normal-projection spatial vector field smooth on the entire displacement
domain, with a strictly positive denominator. The parameter set may have
a boundary. Higher spatial derivatives follow from the general spatial
derivative theorem without differentiating the parameter. -/
theorem normal_projection_vector_field_smooth
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (U : Set P) (V : P × ℝ → ℂ)
    (hV : ContDiffOn ℝ ∞ V (U ×ˢ (univ : Set ℝ)))
    (T : ℝ → ℂ) (κ : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hκ : ContDiff ℝ ∞ κ)
    (hTd : ∀ s, HasDerivAt T (I*(κ s:ℂ)*T s) s)
    (hunit : ∀ s, ‖T s‖=1)
    (δ K r : ℝ) (hK : 0≤K) (hsmall : δ+K*r<1)
    (hcurvature : ∀ s, |κ s|≤K)
    (hclose : ∀ p ∈ U, ∀ x : ℝ, ‖V (p,x)-T x‖≤δ) :
    IsOpen {z : NormalProjectionState | |z.2.1|<r} ∧
      (∀ p ∈ U, ∀ z : NormalProjectionState, |z.2.1|<r →
        0<(conj (T z.1)*V (p,z.1+z.2.1)).re) ∧
      ContDiffOn ℝ ∞ (normalProjectionVectorField T κ V)
        (U ×ˢ {z : NormalProjectionState | |z.2.1|<r}) := by
  let O : Set NormalProjectionState := {z | |z.2.1|<r}
  let D := U ×ˢ O
  have hO : IsOpen O := isOpen_lt
    ((continuous_fst.comp continuous_snd).abs) continuous_const
  have hTlip (a b : ℝ) : ‖T b-T a‖≤K*|b-a| := by
    have hb (s : ℝ) : ‖I*(κ s:ℂ)*T s‖≤K := by
      simpa only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
        hunit,mul_one,one_mul] using hcurvature s
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (univ : Set ℝ)) (C := K)
        (fun x _ => (hTd x).hasDerivWithinAt) (fun x _ => hb x)
        convex_univ (mem_univ a) (mem_univ b)
  have hden (p : P) (hp : p ∈ U) (z : NormalProjectionState) (hz : z ∈ O) :
      0<(conj (T z.1)*V (p,z.1+z.2.1)).re := by
    have hs : conj (T z.1)*T z.1=1 := by rw [Complex.conj_mul',hunit]; simp
    have hd : ‖V (p,z.1+z.2.1)-T z.1‖≤δ+K*|z.2.1| := by
      calc
        _ ≤ ‖V (p,z.1+z.2.1)-T (z.1+z.2.1)‖+‖T (z.1+z.2.1)-T z.1‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ+K*|z.2.1| := add_le_add (hclose p hp _)
          (by simpa using hTlip z.1 (z.1+z.2.1))
    have hr : δ+K*|z.2.1|<1 :=
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hz.le hK)).trans_lt hsmall
    have heq : 1-(conj (T z.1)*V (p,z.1+z.2.1)).re=
        (conj (T z.1)*(T z.1-V (p,z.1+z.2.1))).re := by
      rw [mul_sub,hs,Complex.sub_re,Complex.one_re]
    have hreal : |1-(conj (T z.1)*V (p,z.1+z.2.1)).re|≤δ+K*|z.2.1| := by
      rw [heq]
      calc
        _ ≤ ‖conj (T z.1)*(T z.1-V (p,z.1+z.2.1))‖ := Complex.abs_re_le_norm _
        _ = ‖V (p,z.1+z.2.1)-T z.1‖ := by
          rw [norm_mul,Complex.norm_conj,hunit,one_mul,norm_sub_rev]
        _ ≤ _ := hd
    have hb := (abs_le.mp hreal).2
    linarith only [hb,hr]
  have hp : ContDiff ℝ ∞ (fun w : P × NormalProjectionState => w.1) := contDiff_fst
  have hs : ContDiff ℝ ∞ (fun w : P × NormalProjectionState => w.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hξ : ContDiff ℝ ∞ (fun w : P × NormalProjectionState => w.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have hh : ContDiff ℝ ∞ (fun w : P × NormalProjectionState => w.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have hinput : ContDiff ℝ ∞ (fun w : P × NormalProjectionState => (w.1,w.2.1+w.2.2.1)) :=
    hp.prodMk (hs.add hξ)
  have hVc : ContDiffOn ℝ ∞ (fun w : P × NormalProjectionState => V (w.1,w.2.1+w.2.2.1)) D :=
    hV.comp hinput.contDiffOn (fun w hw => ⟨hw.1,mem_univ _⟩)
  let W : P × NormalProjectionState → ℂ := fun w => conj (T w.2.1)*V (w.1,w.2.1+w.2.2.1)
  let A : P × NormalProjectionState → ℝ := fun w => 1-κ w.2.1*w.2.2.2
  have hW : ContDiffOn ℝ ∞ W D :=
    (Complex.conjCLE.contDiff.comp (hT.comp hs)).contDiffOn.mul hVc
  have hWr : ContDiffOn ℝ ∞ (fun w => (W w).re) D :=
    Complex.reCLM.contDiff.comp_contDiffOn hW
  have hWi : ContDiffOn ℝ ∞ (fun w => (W w).im) D :=
    Complex.imCLM.contDiff.comp_contDiffOn hW
  have hA : ContDiff ℝ ∞ A := contDiff_const.sub ((hκ.comp hs).mul hh)
  have hquot : ContDiffOn ℝ ∞ (fun w => A w/(W w).re) D :=
    hA.contDiffOn.div hWr (fun w hw => ne_of_gt (hden w.1 hw.1 w.2 hw.2))
  have hOne : ContDiffOn ℝ ∞ (fun _ : P × NormalProjectionState => (1:ℝ)) D := contDiffOn_const
  have hG := hOne.prodMk ((hquot.sub hOne).prodMk (hquot.mul hWi))
  refine ⟨hO,hden,?_⟩
  simpa only [normalProjectionVectorField,W,A,D,O] using! hG

end Lemniscate
