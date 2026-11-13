import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-!
# Intrinsic geometry of an actual arbitrary-speed planar immersion

All fields are defined from the position and its actual derivatives. The only
geometric hypotheses are smoothness and nonvanishing of its spatial derivative.
No Frenet equation, curvature evolution, stress identity, or force is supplied
as an independent field. No time evolution or global arclength change of
variables is claimed here.

The elementary complex unit-frame argument below follows the already checked
`LengthGrowth/CurveFromPosition.lean` proof. The stress product-rule argument
follows `LengthGrowth/ElasticStress.lean`, with the actual material speed kept.
Those frozen files are unchanged; this module imports Mathlib only.
-/

noncomputable section
open scoped ComplexConjugate ContDiff

namespace LengthGrowth.ActualFlow

def speed (γ : ℝ → ℂ) (u : ℝ) : ℝ := ‖deriv γ u‖

def arcDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ → ℂ) (f : ℝ → E) (u : ℝ) : E :=
  (speed γ u)⁻¹ • deriv f u

def tangent (γ : ℝ → ℂ) : ℝ → ℂ := arcDerivative γ γ
def normal (γ : ℝ → ℂ) (u : ℝ) : ℂ := Complex.I * tangent γ u

/-- Actual signed curvature; below it is identified with `<D_s T,N>`. -/
def curvature (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  (conj (tangent γ u) * deriv (tangent γ) u).im / speed γ u

def curvatureGradient (γ : ℝ → ℂ) : ℝ → ℝ := arcDerivative γ (curvature γ)
def curvatureSecond (γ : ℝ → ℂ) : ℝ → ℝ := arcDerivative γ (curvatureGradient γ)
def force (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  curvatureSecond γ u + curvature γ u ^ 3 / 2
def stress (γ : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((curvature γ u : ℂ) ^ 2 / 2) * tangent γ u +
    (curvatureGradient γ u : ℂ) * normal γ u

variable {γ : ℝ → ℂ}

theorem speed_pos (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) : 0 < speed γ u :=
  norm_pos_iff.mpr (hreg u)

theorem speed_smooth (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) :
    ContDiff ℝ ∞ (speed γ) := by
  exact ((contDiff_infty_iff_deriv.mp hγ).2).norm ℝ hreg

theorem arcDerivative_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (arcDerivative γ f) := by
  exact ((speed_smooth hγ hreg).inv (fun u => (speed_pos hreg u).ne')).smul
    (contDiff_infty_iff_deriv.mp hf).2

theorem tangent_smooth (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) :
    ContDiff ℝ ∞ (tangent γ) := arcDerivative_smooth hγ hreg hγ

theorem normal_smooth (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) :
    ContDiff ℝ ∞ (normal γ) :=
  contDiff_const.mul (tangent_smooth hγ hreg)

theorem curvature_smooth (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) :
    ContDiff ℝ ∞ (curvature γ) := by
  have ht := tangent_smooth hγ hreg
  exact (Complex.imCLM.contDiff.comp
    ((Complex.conjCLE.contDiff.comp ht).mul (contDiff_infty_iff_deriv.mp ht).2)).div
    (speed_smooth hγ hreg) (fun u => (speed_pos hreg u).ne')

theorem curvatureGradient_smooth (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) : ContDiff ℝ ∞ (curvatureGradient γ) :=
  arcDerivative_smooth hγ hreg (curvature_smooth hγ hreg)

theorem curvatureSecond_smooth (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) : ContDiff ℝ ∞ (curvatureSecond γ) :=
  arcDerivative_smooth hγ hreg (curvatureGradient_smooth hγ hreg)

theorem force_smooth (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) :
    ContDiff ℝ ∞ (force γ) :=
  (curvatureSecond_smooth hγ hreg).add
    (((curvature_smooth hγ hreg).pow 3).div_const 2)

theorem tangent_unit (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    ‖tangent γ u‖ = 1 := by
  change ‖(‖deriv γ u‖⁻¹ : ℝ) • deriv γ u‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hreg u))]

theorem normal_unit (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    ‖normal γ u‖ = 1 := by simp [normal, tangent_unit hreg]

theorem tangent_normal_orthogonal (u : ℝ) :
    inner ℝ (tangent γ u) (normal γ u) = 0 := by
  rw [Complex.inner]
  simp only [normal, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem speed_smul_arcDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hreg : ∀ u, deriv γ u ≠ 0) (f : ℝ → E) (u : ℝ) :
    speed γ u • arcDerivative γ f u = deriv f u := by
  rw [arcDerivative, smul_smul, mul_inv_cancel₀ (speed_pos hreg u).ne', one_smul]

theorem hasDerivAt_speed_smul_arcDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hreg : ∀ u, deriv γ u ≠ 0) {f : ℝ → E} (hf : Differentiable ℝ f) (u : ℝ) :
    HasDerivAt f (speed γ u • arcDerivative γ f u) u := by
  rw [speed_smul_arcDerivative hreg]
  exact (hf u).hasDerivAt

theorem position_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (u : ℝ) : HasDerivAt γ (speed γ u • tangent γ u) u :=
  hasDerivAt_speed_smul_arcDerivative hreg (hγ.differentiable (by simp)) u

/-- Algebraic Frenet identity for a genuinely unit complex field. The unit
assumption here will be discharged by the normalized actual position. -/
theorem unit_frame_deriv {T : ℝ → ℂ} (hT : Differentiable ℝ T)
    (hu : ∀ u, ‖T u‖ = 1) (u : ℝ) :
    deriv T u = ((conj (T u) * deriv T u).im : ℂ) * (Complex.I * T u) := by
  have hunit (s : ℝ) : T s * conj (T s) = 1 := by
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, hu]
  have hconst : (fun s => conj (T s) * T s) = (fun _ => (1 : ℂ)) := by
    funext s
    rw [mul_comm, hunit s]
  have hd := ((hT u).hasDerivAt.star).mul (hT u).hasDerivAt
  change HasDerivAt (fun s => conj (T s) * T s)
    (conj (deriv T u) * T u + conj (T u) * deriv T u) u at hd
  rw [hconst] at hd
  have hz := hd.unique (hasDerivAt_const u (1 : ℂ))
  have hre : (conj (T u) * deriv T u).re = 0 := by
    have h := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.zero_re] at h ⊢
    linarith
  have hdecomp : conj (T u) * deriv T u =
      ((conj (T u) * deriv T u).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  calc
    deriv T u = (T u * conj (T u)) * deriv T u := by rw [hunit, one_mul]
    _ = T u * (conj (T u) * deriv T u) := by ring
    _ = T u * (((conj (T u) * deriv T u).im : ℂ) * Complex.I) :=
      congrArg (fun z => T u * z) hdecomp
    _ = _ := by ring

theorem curvature_mul_speed (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    curvature γ u * speed γ u = (conj (tangent γ u) * deriv (tangent γ) u).im := by
  exact div_mul_cancel₀ _ (speed_pos hreg u).ne'

theorem tangent_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (u : ℝ) : HasDerivAt (tangent γ)
      (((speed γ u * curvature γ u : ℝ) : ℂ) * normal γ u) u := by
  have ht := (tangent_smooth hγ hreg).differentiable (by simp)
  have hd := (ht u).hasDerivAt
  rw [unit_frame_deriv ht (tangent_unit hreg) u] at hd
  have hc : speed γ u * curvature γ u =
      (conj (tangent γ u) * deriv (tangent γ) u).im := by
    rw [mul_comm, curvature_mul_speed hreg]
  simpa only [hc, normal] using hd

theorem normal_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (u : ℝ) : HasDerivAt (normal γ)
      (-((speed γ u * curvature γ u : ℝ) : ℂ) * tangent γ u) u := by
  have hd := (tangent_hasDerivAt hγ hreg u).const_mul Complex.I
  have he : Complex.I * (((speed γ u * curvature γ u : ℝ) : ℂ) * normal γ u) =
      -((speed γ u * curvature γ u : ℝ) : ℂ) * tangent γ u := by
    dsimp [normal]
    calc
      _ = (Complex.I * Complex.I) *
          (((speed γ u * curvature γ u : ℝ) : ℂ) * tangent γ u) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he] at hd
  exact hd

theorem arcDerivative_tangent (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    arcDerivative γ (tangent γ) u = curvature γ u • normal γ u := by
  rw [arcDerivative, (tangent_hasDerivAt hγ hreg u).deriv]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp [(speed_pos hreg u).ne']

theorem arcDerivative_normal (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    arcDerivative γ (normal γ) u = -(curvature γ u) • tangent γ u := by
  rw [arcDerivative, (normal_hasDerivAt hγ hreg u).deriv]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_neg]
  field_simp [(speed_pos hreg u).ne']

theorem curvature_eq_inner_arcDerivative (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    curvature γ u = inner ℝ (arcDerivative γ (tangent γ) u) (normal γ u) := by
  rw [arcDerivative_tangent hγ hreg, real_inner_smul_left,
    real_inner_self_eq_norm_sq, normal_unit hreg]
  simp

theorem curvature_hasDerivAt (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) : HasDerivAt (curvature γ)
      (speed γ u * curvatureGradient γ u) u :=
  hasDerivAt_speed_smul_arcDerivative hreg
    ((curvature_smooth hγ hreg).differentiable (by simp)) u

theorem curvatureGradient_hasDerivAt (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) : HasDerivAt (curvatureGradient γ)
      (speed γ u * curvatureSecond γ u) u :=
  hasDerivAt_speed_smul_arcDerivative hreg
    ((curvatureGradient_smooth hγ hreg).differentiable (by simp)) u

/-- The actual material derivative of stress includes the actual speed. -/
theorem stress_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (u : ℝ) : HasDerivAt (stress γ)
      (((speed γ u * force γ u : ℝ) : ℂ) * normal γ u) u := by
  have hk := (curvature_hasDerivAt hγ hreg u).ofReal_comp
  have hk₁ := (curvatureGradient_hasDerivAt hγ hreg u).ofReal_comp
  have hd := HasDerivAt.add
    (HasDerivAt.mul (HasDerivAt.div_const (HasDerivAt.mul hk hk) 2)
      (tangent_hasDerivAt hγ hreg u))
    (HasDerivAt.mul hk₁ (normal_hasDerivAt hγ hreg u))
  convert! hd using 1
  · funext s
    simp [stress, pow_two]
  · simp only [force, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Pi.mul_apply]
    ring

/-- The intrinsic arclength stress identity, with no supplied Frenet data. -/
theorem arcDerivative_stress (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (u : ℝ) : arcDerivative γ (stress γ) u = (force γ u : ℂ) * normal γ u := by
  rw [arcDerivative, (stress_hasDerivAt hγ hreg u).deriv]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp [(speed_pos hreg u).ne']

theorem stress_smooth (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) :
    ContDiff ℝ ∞ (stress γ) := by
  exact ((((Complex.ofRealCLM.contDiff.comp (curvature_smooth hγ hreg)).pow 2).div_const 2).mul
    (tangent_smooth hγ hreg)).add
    ((Complex.ofRealCLM.contDiff.comp (curvatureGradient_smooth hγ hreg)).mul
      (normal_smooth hγ hreg))

end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.tangent_hasDerivAt
#print axioms LengthGrowth.ActualFlow.curvature_eq_inner_arcDerivative
#print axioms LengthGrowth.ActualFlow.stress_hasDerivAt
#print axioms LengthGrowth.ActualFlow.arcDerivative_stress

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Intrinsic curve audit failed: {name} depends on {axiomName}"
      count := count + 1
  unless count > 0 do throwError "No actual curve declarations audited"
  logInfo m!"ACTUAL_INTRINSIC_CURVE_AUDIT {count}: standard three axioms only."
