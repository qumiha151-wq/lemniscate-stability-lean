import Lean.Util.CollectAxioms
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Spatial geometry, time-space commutation, and compact parameter integration for the
Migration project. These proofs reuse the corresponding lemmas in IntrinsicCurve,
MixedPartials, FamilyRegularity, FamilyDerivatives, CompactParameterIntegral, and
IntervalL2. The position determines the metric, frame, curvature and elastic force. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ComplexConjugate ContDiff Topology Interval
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow
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

section Schwarz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def partialTime (f : ℝ × ℝ → E) (x : ℝ × ℝ) : E :=
  fderiv ℝ f x (1, 0)

def partialSpace (f : ℝ × ℝ → E) (x : ℝ × ℝ) : E :=
  fderiv ℝ f x (0, 1)

theorem deriv_time_eq_partialTime {f : ℝ × ℝ → E} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun t => f (t, x.2)) x.1 = partialTime f x := by
  exact (hf.hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))).deriv

theorem deriv_space_eq_partialSpace {f : ℝ × ℝ → E} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun u => f (x.1, u)) x.2 = partialSpace f x := by
  exact (hf.hasFDerivAt.comp_hasDerivAt x.2
    ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))).deriv

theorem fderiv_apply_fixed {c : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] E}
    {x : ℝ × ℝ} (hc : DifferentiableAt ℝ c x) (v w : ℝ × ℝ) :
    fderiv ℝ (fun y => c y v) x w = fderiv ℝ c x w v := by
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

theorem actual_partials_commute {f : ℝ × ℝ → E} {x : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    partialTime (partialSpace f) x = partialSpace (partialTime f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) x (1, 0) =
    fderiv ℝ (fun y => fderiv ℝ f y (1, 0)) x (0, 1)
  rw [fderiv_apply_fixed hd, fderiv_apply_fixed hd]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1)
end Schwarz

structure SmoothPeriodicImmersion (I : Set ℝ) where
  time_open : IsOpen I
  period : ℝ
  period_pos : 0 < period
  position : ℝ → ℝ → ℂ
  joint_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => position z.1 z.2)
    (I ×ˢ (univ : Set ℝ))
  periodic : ∀ t ∈ I, Function.Periodic (position t) period
  immersion : ∀ t ∈ I, ∀ u, deriv (position t) u ≠ 0

section JointHelpers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : Set ℝ} {f : ℝ → ℝ → E}

theorem joint_smooth_space_slice
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (f t) :=
  hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht, mem_univ _⟩)

theorem joint_smooth_time_slice
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    (u : ℝ) : ContDiffOn ℝ ∞ (fun t => f t u) I :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, mem_univ u⟩)

theorem joint_smooth_deriv_space (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (f z.1) z.2) (I ×ˢ (univ : Set ℝ)) := by
  have hS : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hp : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => f w.1 w.2) z (0, 1))
      (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  apply hp.congr
  intro z hz
  have hd := (hf.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
  exact (hd.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv

theorem joint_smooth_deriv_time (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (fun t => f t z.2) z.1)
      (I ×ˢ (univ : Set ℝ)) := by
  have hS : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hp : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => f w.1 w.2) z (1, 0))
      (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  apply hp.congr
  intro z hz
  have hd := (hf.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
  exact (hd.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv

theorem joint_smooth_time_hasDerivAt (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => f x u) (deriv (fun x => f x u) t) t :=
  (((joint_smooth_time_slice hf u).differentiableOn (by simp) t ht).differentiableAt
    (hI.mem_nhds ht)).hasDerivAt

end JointHelpers

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def velocity (t u : ℝ) : ℂ := deriv (fun x => c.position x u) t

/-- The tangent component of the actual arclength derivative of velocity. -/
def velocityGradientTangent (t u : ℝ) : ℝ :=
  inner ℝ (arcDerivative (c.position t) (c.velocity t) u) (tangent (c.position t) u)

/-- The normal component of the actual arclength derivative of velocity. -/
def velocityGradientNormal (t u : ℝ) : ℝ :=
  inner ℝ (arcDerivative (c.position t) (c.velocity t) u) (normal (c.position t) u)

theorem position_slice_smooth {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (c.position t) :=
  joint_smooth_space_slice c.joint_smooth ht

theorem velocity_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => c.velocity z.1 z.2) (I ×ˢ (univ : Set ℝ)) :=
  joint_smooth_deriv_time c.time_open c.joint_smooth

theorem velocity_slice_smooth {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (c.velocity t) :=
  joint_smooth_space_slice c.velocity_joint_smooth ht

theorem position_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => c.position x u) (c.velocity t u) t :=
  joint_smooth_time_hasDerivAt c.time_open c.joint_smooth ht u

theorem speed_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => speed (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  (joint_smooth_deriv_space c.time_open c.joint_smooth).norm ℝ
    (fun z hz => c.immersion z.1 hz.1 z.2)

theorem arcDerivative_joint_smooth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => arcDerivative (c.position z.1) (f z.1) z.2)
      (I ×ˢ (univ : Set ℝ)) :=
  (c.speed_joint_smooth.inv (fun z hz => (speed_pos (c.immersion z.1 hz.1) z.2).ne')).smul
    (joint_smooth_deriv_space c.time_open hf)

theorem tangent_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => tangent (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.arcDerivative_joint_smooth c.joint_smooth

theorem normal_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => normal (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  contDiffOn_const.mul c.tangent_joint_smooth

theorem curvature_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => curvature (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) := by
  have hnum := Complex.imCLM.contDiff.comp_contDiffOn
    ((Complex.conjCLE.contDiff.comp_contDiffOn c.tangent_joint_smooth).mul
      (joint_smooth_deriv_space (f := fun t => tangent (c.position t))
        c.time_open c.tangent_joint_smooth))
  exact hnum.div c.speed_joint_smooth
    (fun z hz => (speed_pos (c.immersion z.1 hz.1) z.2).ne')

theorem curvatureGradient_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => curvatureGradient (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.arcDerivative_joint_smooth (f := fun t => curvature (c.position t)) c.curvature_joint_smooth

theorem curvatureSecond_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => curvatureSecond (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.arcDerivative_joint_smooth (f := fun t => curvatureGradient (c.position t))
    c.curvatureGradient_joint_smooth

theorem force_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => force (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.curvatureSecond_joint_smooth.add ((c.curvature_joint_smooth.pow 3).div_const 2)
end SmoothPeriodicImmersion

theorem actual_time_space_deriv_commute {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ} {f : ℝ → ℝ → E}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    deriv (fun x => deriv (f x) u) t =
      deriv (fun y => deriv (fun x => f x y) t) u := by
  let F : ℝ × ℝ → E := fun z => f z.1 z.2
  have hS : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hdf (z : ℝ × ℝ) (hz : z ∈ I ×ˢ (univ : Set ℝ)) : DifferentiableAt ℝ F z :=
    (hf.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
  have hsp : ContDiffOn ℝ ∞ (partialSpace F) (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  have htp : ContDiffOn ℝ ∞ (partialTime F) (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  have hz : (t, u) ∈ I ×ˢ (univ : Set ℝ) := ⟨ht, mem_univ u⟩
  calc
    _ = deriv (fun x => partialSpace F (x, u)) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hI.mem_nhds ht] with x hx
      exact deriv_space_eq_partialSpace (hdf (x, u) ⟨hx, mem_univ u⟩)
    _ = partialTime (partialSpace F) (t, u) :=
      deriv_time_eq_partialTime
        ((hsp.differentiableOn (by simp) (t, u) hz).differentiableAt (hS.mem_nhds hz))
    _ = partialSpace (partialTime F) (t, u) :=
      actual_partials_commute ((hf (t, u) hz).contDiffAt (hS.mem_nhds hz) |>.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    _ = deriv (fun y => partialTime F (t, y)) u :=
      (deriv_space_eq_partialSpace
        ((htp.differentiableOn (by simp) (t, u) hz).differentiableAt (hS.mem_nhds hz))).symm
    _ = _ := by
      congr 1
      funext y
      exact (deriv_time_eq_partialTime (hdf (t, y) ⟨ht, mem_univ y⟩)).symm

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem position_space_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => deriv (c.position x) u) (deriv (c.velocity t) u) t := by
  have h := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => deriv (c.position x))
    (joint_smooth_deriv_space c.time_open c.joint_smooth) ht u
  rw [actual_time_space_deriv_commute c.time_open c.joint_smooth ht u] at h
  exact h

theorem speed_mul_velocityGradientTangent {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    speed (c.position t) u * c.velocityGradientTangent t u =
      inner ℝ (deriv (c.velocity t) u) (tangent (c.position t) u) := by
  simp only [velocityGradientTangent, arcDerivative, real_inner_smul_left]
  rw [← mul_assoc, mul_inv_cancel₀ (speed_pos (c.immersion t ht) u).ne', one_mul]

/-- The metric time derivative is derived from the norm of the actual position derivative. -/
theorem speed_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => speed (c.position x) u)
      (speed (c.position t) u * c.velocityGradientTangent t u) t := by
  have hg := joint_smooth_time_hasDerivAt c.time_open
    (f := fun x => speed (c.position x)) c.speed_joint_smooth ht u
  have hsq := (c.position_space_time_hasDerivAt ht u).norm_sq
  have he := (hg.pow 2).unique hsq
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at he
  have hp := (position_hasDerivAt (c.position_slice_smooth ht) (c.immersion t ht) u).deriv
  have hne := (speed_pos (c.immersion t ht) u).ne'
  have hgt : deriv (fun x => speed (c.position x) u) t =
      inner ℝ (tangent (c.position t) u) (deriv (c.velocity t) u) := by
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hne)
    calc
      _ = 2 * inner ℝ (deriv (c.position t) u) (deriv (c.velocity t) u) := he
      _ = _ := by rw [hp, real_inner_smul_left]; ring
  rw [hgt, real_inner_comm, ← c.speed_mul_velocityGradientTangent ht u] at hg
  exact hg
end SmoothPeriodicImmersion

private theorem continuousOn_space_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b t : ℝ} (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (ht : t ∈ I) : ContinuousOn (F t) (uIcc a b) :=
  hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hu => ⟨ht, hu⟩)

private theorem continuousOn_time_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b u : ℝ} (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (hu : u ∈ uIcc a b) : ContinuousOn (fun t => F t u) I :=
  hF.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, hu⟩)

/-- Spatial integrability on the fixed compact parameter interval. -/
theorem intervalIntegrable_parameter_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b t : ℝ} (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (ht : t ∈ I) : IntervalIntegrable (F t) volume a b :=
  (continuousOn_space_slice hF ht).intervalIntegrable

/-- Continuity up to both endpoints of any compact time set; no time derivative is required. -/
theorem continuousOn_intervalIntegral_of_isCompact {K : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b : ℝ} (hK : IsCompact K)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (K ×ˢ uIcc a b)) :
    ContinuousOn (fun t => ∫ u in a..b, F t u) K := by
  obtain ⟨M, hM⟩ := (hK.prod isCompact_uIcc).bddAbove_image hF.norm
  intro t ht
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => M)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((continuousOn_space_slice hF hx).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ae_of_all _ fun u hu => hM (mem_image_of_mem
      (fun z : ℝ × ℝ => ‖F z.1 z.2‖)
      (show (x, u) ∈ K ×ˢ uIcc a b from ⟨hx, uIoc_subset_uIcc hu⟩))
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun u hu =>
      continuousOn_time_slice hF (uIoc_subset_uIcc hu) t ht

/-- A closed forward time slab is covered without any backwards extension. -/
theorem continuousOn_intervalIntegral_on_closed_slab {F : ℝ → ℝ → ℝ}
    {a b c d : ℝ}
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (Icc c d ×ˢ uIcc a b)) :
    ContinuousOn (fun t => ∫ u in a..b, F t u) (Icc c d) :=
  continuousOn_intervalIntegral_of_isCompact isCompact_Icc hF

/-- Continuity on an open time domain needs only joint continuity. -/
theorem continuousOn_intervalIntegral_of_isOpen {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    {a b : ℝ} (hI : IsOpen I)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b)) :
    ContinuousOn (fun t => ∫ u in a..b, F t u) I := by
  intro t ht
  obtain ⟨r, hr, hrI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hc := continuousOn_intervalIntegral_of_isCompact (isCompact_closedBall t r)
    (hF.mono (show Metric.closedBall t r ×ˢ uIcc a b ⊆ I ×ˢ uIcc a b from
      fun _ hz => ⟨hrI hz.1, hz.2⟩))
  exact ((hc t (Metric.mem_closedBall_self hr.le)).continuousAt
    (Metric.closedBall_mem_nhds t hr)).continuousWithinAt

/-- A true time derivative passes through the fixed interval integral. The bound
on the derivative is obtained from a compact time neighborhood, not assumed. -/
theorem hasDerivAt_intervalIntegral_of_continuousOn {I : Set ℝ}
    {F D : ℝ → ℝ → ℝ} {a b t : ℝ} (hI : IsOpen I)
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ uIcc a b))
    (hD : ContinuousOn (fun z : ℝ × ℝ => D z.1 z.2) (I ×ˢ uIcc a b))
    (hd : ∀ x ∈ I, ∀ u ∈ uIcc a b, HasDerivAt (fun y => F y u) (D x u) x)
    (ht : t ∈ I) :
    HasDerivAt (fun x => ∫ u in a..b, F x u) (∫ u in a..b, D t u) t := by
  obtain ⟨r, hr, hrI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hDc : ContinuousOn (fun z : ℝ × ℝ => D z.1 z.2)
      (Metric.closedBall t r ×ˢ uIcc a b) :=
    hD.mono (fun _ hz => ⟨hrI hz.1, hz.2⟩)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t r).prod isCompact_uIcc).bddAbove_image hDc.norm
  have hset : HasDerivAt (fun x => ∫ u in uIoc a b, F x u)
      (∫ u in uIoc a b, D t u) t := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (uIoc a b))
      (F' := D) (bound := fun _ => M)
      (s := Metric.closedBall t r) (Metric.closedBall_mem_nhds t hr) ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [hI.mem_nhds ht] with x hx
      exact ((continuousOn_space_slice hF hx).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
    · exact (intervalIntegrable_parameter_slice hF ht).def'
    · exact ((continuousOn_space_slice hD ht).mono uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu x hx
      exact hM (mem_image_of_mem (fun z : ℝ × ℝ => ‖D z.1 z.2‖)
        (show (x, u) ∈ Metric.closedBall t r ×ˢ uIcc a b from
          ⟨hx, uIoc_subset_uIcc hu⟩))
    · exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume a b).def'
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu x hx
      exact hd x (hrI hx) u (uIoc_subset_uIcc hu)
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul] using
    hset.const_mul (if a ≤ b then (1 : ℝ) else -1)

theorem interval_integral_mul_sq_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b) :
    (∫ s in a..b, f s * g s)^2 ≤
      (∫ s in a..b, f s ^ 2) * (∫ s in a..b, g s ^ 2) := by
  let A := ∫ s in a..b, f s ^ 2
  let B := ∫ s in a..b, f s * g s
  let C := ∫ s in a..b, g s ^ 2
  have hpoly : ∀ t : ℝ, 0 ≤ C * (t*t) + (2*B)*t + A := by
    intro t
    have hpos : 0 ≤ ∫ s in a..b, (f s + t * g s)^2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => sq_nonneg _)
    have heq : (fun s => (f s + t*g s)^2) =
        (fun s => f s^2 + (2*t)*(f s*g s) + (t*t)*(g s^2)) := by
      funext s
      ring
    rw [heq, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hpos
    · dsimp [A, B, C]
      nlinarith
    · exact (hf.pow 2).intervalIntegrable _ _
    · exact ((hf.mul hg).const_mul (2*t)).intervalIntegrable _ _
    · exact ((hf.pow 2).add ((hf.mul hg).const_mul (2*t))).intervalIntegrable _ _
    · exact ((hg.pow 2).const_mul (t*t)).intervalIntegrable _ _
  have hdisc := discrim_le_zero hpoly
  dsimp [discrim] at hdisc
  change B^2 ≤ A*C
  nlinarith

theorem interval_integral_abs_mul_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b) :
    (∫ s in a..b, |f s * g s|) ≤
      Real.sqrt (∫ s in a..b, f s ^ 2) * Real.sqrt (∫ s in a..b, g s ^ 2) := by
  have h := interval_integral_mul_sq_le hf.abs hg.abs hab
  simp only [sq_abs] at h
  have hA := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun s => sq_nonneg (f s))
  have hB := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun s => sq_nonneg (g s))
  have hI := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun s => abs_nonneg (f s*g s))
  have hAs := Real.sq_sqrt hA
  have hBs := Real.sq_sqrt hB
  have hAB : (Real.sqrt (∫ s in a..b, f s^2) *
      Real.sqrt (∫ s in a..b, g s^2))^2 =
      (∫ s in a..b, f s^2)*(∫ s in a..b, g s^2) := by
    rw [mul_pow, hAs, hBs]
  have hn := mul_nonneg (Real.sqrt_nonneg (∫ s in a..b, f s^2))
    (Real.sqrt_nonneg (∫ s in a..b, g s^2))
  rw [show (fun s => |f s| * |g s|) = (fun s => |f s*g s|) by
    funext s; exact (abs_mul _ _).symm] at h
  nlinarith

end MigrationGeometry.Flow
