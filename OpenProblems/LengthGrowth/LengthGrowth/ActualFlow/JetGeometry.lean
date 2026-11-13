import LengthGrowth.ActualFlow.IntrinsicCurve
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Actual spatial jets and the two-jet curvature formula. The position is
arbitrarily parametrized; all jets are iterated actual derivatives. -/

noncomputable section
open scoped ComplexConjugate ContDiff

namespace LengthGrowth.ActualFlow

def positionJet1 (γ : ℝ → ℂ) : ℝ → ℂ := deriv γ
def positionJet2 (γ : ℝ → ℂ) : ℝ → ℂ := deriv (positionJet1 γ)
def positionJet3 (γ : ℝ → ℂ) : ℝ → ℂ := deriv (positionJet2 γ)
def positionJet4 (γ : ℝ → ℂ) : ℝ → ℂ := deriv (positionJet3 γ)

def determinant (v a : ℂ) : ℝ := (conj v * a).im

def jetNormSq (γ : ℝ → ℂ) (u : ℝ) : ℝ := ‖positionJet1 γ u‖ ^ 2
def jetNormSqFirst (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  2 * inner ℝ (positionJet1 γ u) (positionJet2 γ u)
def jetNormSqSecond (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  2 * (inner ℝ (positionJet2 γ u) (positionJet2 γ u) +
    inner ℝ (positionJet1 γ u) (positionJet3 γ u))
def jetDet (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  determinant (positionJet1 γ u) (positionJet2 γ u)
def jetDetFirst (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  determinant (positionJet1 γ u) (positionJet3 γ u)
def jetDetSecond (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  determinant (positionJet2 γ u) (positionJet3 γ u) +
    determinant (positionJet1 γ u) (positionJet4 γ u)

theorem determinant_eq_inner (v a : ℂ) :
    determinant v a = inner ℝ a (Complex.I * v) := by
  rw [Complex.inner]
  simp only [determinant, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im]
  ring

theorem determinant_smul_left (r : ℝ) (v a : ℂ) :
    determinant (r • v) a = r * determinant v a := by
  simp only [determinant, Complex.real_smul, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem determinant_smul_right (r : ℝ) (v a : ℂ) :
    determinant v (r • a) = r * determinant v a := by
  simp only [determinant, Complex.real_smul, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem determinant_add_right (v a b : ℂ) :
    determinant v (a+b) = determinant v a + determinant v b := by
  simp only [determinant, mul_add, Complex.add_im]

theorem determinant_self (v : ℂ) : determinant v v = 0 := by
  simp only [determinant, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

variable {γ : ℝ → ℂ}

theorem positionJet1_smooth (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (positionJet1 γ) := (contDiff_infty_iff_deriv.mp hγ).2
theorem positionJet2_smooth (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (positionJet2 γ) :=
  (contDiff_infty_iff_deriv.mp (positionJet1_smooth hγ)).2
theorem positionJet3_smooth (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (positionJet3 γ) :=
  (contDiff_infty_iff_deriv.mp (positionJet2_smooth hγ)).2
theorem positionJet4_smooth (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (positionJet4 γ) :=
  (contDiff_infty_iff_deriv.mp (positionJet3_smooth hγ)).2

theorem positionJet1_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (positionJet1 γ) (positionJet2 γ u) u :=
  ((positionJet1_smooth hγ).differentiable (by simp) u).hasDerivAt
theorem positionJet2_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (positionJet2 γ) (positionJet3 γ u) u :=
  ((positionJet2_smooth hγ).differentiable (by simp) u).hasDerivAt
theorem positionJet3_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (positionJet3 γ) (positionJet4 γ u) u :=
  ((positionJet3_smooth hγ).differentiable (by simp) u).hasDerivAt

theorem jetNormSq_eq_speed_sq (u : ℝ) : jetNormSq γ u = speed γ u ^ 2 := rfl

theorem jetNormSq_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (jetNormSq γ) (jetNormSqFirst γ u) u :=
  (positionJet1_hasDerivAt hγ u).norm_sq

theorem jetNormSqFirst_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (jetNormSqFirst γ) (jetNormSqSecond γ u) u := by
  convert! ((positionJet1_hasDerivAt hγ u).inner ℝ
    (positionJet2_hasDerivAt hγ u)).const_mul 2 using 1
  simp only [jetNormSqSecond]
  ring

theorem jetDet_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (jetDet γ) (jetDetFirst γ u) u := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u
    ((positionJet1_hasDerivAt hγ u).star.mul (positionJet2_hasDerivAt hγ u))
  convert! hd using 1
  simp only [jetDetFirst, determinant, Complex.imCLM_apply, Complex.add_im, Complex.star_def,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem jetDetFirst_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (jetDetFirst γ) (jetDetSecond γ u) u := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u
    ((positionJet1_hasDerivAt hγ u).star.mul (positionJet3_hasDerivAt hγ u))
  convert! hd using 1

theorem speed_hasDerivAt_jet (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    HasDerivAt (speed γ) (jetNormSqFirst γ u / (2 * speed γ u)) u := by
  have hg := ((speed_smooth hγ hreg).differentiable (by simp) u).hasDerivAt
  have he := (hg.pow 2).unique (jetNormSq_hasDerivAt hγ u)
  have hd : deriv (speed γ) u = jetNormSqFirst γ u / (2 * speed γ u) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) (speed_pos hreg u).ne')).2
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at he
    nlinarith [he]
  rw [hd] at hg
  exact hg

theorem positionJet1_eq_speed_tangent (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    positionJet1 γ u = speed γ u • tangent γ u :=
  (position_hasDerivAt hγ hreg u).deriv

theorem positionJet2_eq_frame (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    positionJet2 γ u = speed γ u • ((speed γ u * curvature γ u) • normal γ u) +
      deriv (speed γ) u • tangent γ u := by
  have hg := ((speed_smooth hγ hreg).differentiable (by simp) u).hasDerivAt
  have hT : HasDerivAt (tangent γ) ((speed γ u * curvature γ u) • normal γ u) u := by
    simpa only [Complex.real_smul] using tangent_hasDerivAt hγ hreg u
  have he : positionJet1 γ = (fun x => speed γ x • tangent γ x) :=
    funext (positionJet1_eq_speed_tangent hγ hreg)
  have hd := hg.smul hT
  change HasDerivAt (fun x => speed γ x • tangent γ x) _ u at hd
  rw [← he] at hd
  exact hd.deriv

theorem jetDet_eq_speed_cubed_curvature (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    jetDet γ u = speed γ u ^ 3 * curvature γ u := by
  have hTN : determinant (tangent γ u) (normal γ u) = 1 := by
    rw [determinant_eq_inner]
    change inner ℝ (normal γ u) (normal γ u) = 1
    rw [real_inner_self_eq_norm_sq, normal_unit hreg]
    norm_num
  rw [jetDet, positionJet1_eq_speed_tangent hγ hreg,
    positionJet2_eq_frame hγ hreg, determinant_smul_left,
    determinant_add_right, determinant_smul_right, determinant_smul_right,
    determinant_smul_right, hTN, determinant_self]
  ring

/-- Signed curvature expressed using actual first and second position jets. -/
theorem curvature_eq_two_jet (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    curvature γ u = jetDet γ u / speed γ u ^ 3 := by
  apply (eq_div_iff (pow_ne_zero 3 (speed_pos hreg u).ne')).2
  rw [jetDet_eq_speed_cubed_curvature hγ hreg]
  ring

end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.curvature_eq_two_jet

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless allowed.contains a do throwError "Jet geometry audit failed: {name} uses {a}"
      count := count + 1
  logInfo m!"ACTUAL_JET_GEOMETRY_AUDIT {count}: standard three axioms only."
