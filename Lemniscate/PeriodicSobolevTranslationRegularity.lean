import Lemniscate.PeriodicSobolevTranslation
import Lemniscate.ParameterDerivativeEstimate
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-! Differentiability of the actual L2 translation orbit produces the
complete weak derivative jet.  Only the L2 orbit is differentiated; no
parameter derivative on a higher Sobolev space is required.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

private def translationCoefficient (k : ℤ) : CircleL2 T →L[ℂ] ℂ :=
  innerSL ℂ (fourierBasis (T := T) k)

private theorem translation_coefficient_apply (k : ℤ) (f : CircleL2 T) :
    translationCoefficient T k f = fourierCoeff f k := by
  change inner ℂ (fourierBasis (T := T) k) f = fourierCoeff f k
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

private theorem translation_mode_deriv (k : ℤ) (t a : ℝ) :
    HasDerivAt (fun b : ℝ => fourier k ((b*t:ℝ) : AddCircle T))
      (((t:ℂ)*circleFrequencyFactor T k)*fourier k ((a*t:ℝ) : AddCircle T)) a := by
  convert! (hasDerivAt_circle_fourier T k (a*t)).scomp a
    ((hasDerivAt_id a).mul_const t) using 1
  simp only [one_mul,real_smul]
  ring

private theorem translation_mode_iterated_deriv (k : ℤ) (t : ℝ) (i : ℕ) :
    iteratedDeriv i (fun a : ℝ => fourier k ((a*t:ℝ) : AddCircle T)) =
      fun a => ((t:ℂ)*circleFrequencyFactor T k)^i*
        fourier k ((a*t:ℝ) : AddCircle T) := by
  induction i with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ i hi =>
    rw [iteratedDeriv_succ,hi]
    funext a
    rw [((translation_mode_deriv T k t a).const_mul
      (((t:ℂ)*circleFrequencyFactor T k)^i)).deriv]
    rw [pow_succ]
    ring

private theorem cancel_translation_scale (t : ℝ) (ht : t ≠ 0)
    (ω z : ℂ) (i : ℕ) :
    (((t⁻¹)^i:ℝ):ℂ)*((((t:ℂ)*ω)^i)*z) = ω^i*z := by
  have htC : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  rw [← mul_assoc,← mul_pow]
  have hc : (t:ℂ)⁻¹*((t:ℂ)*ω) = ω := by rw [← mul_assoc,inv_mul_cancel₀ htC,one_mul]
  rw [hc]

/-- An n-times differentiable L2 translation orbit at a nonzero physical
time yields the actual complete Hn element. Every weak derivative is the
corresponding orbit derivative divided by that time to the same order. -/
theorem circle_sobolev_of_translation_contDiffAt
    (n : ℕ) (t : ℝ) (ht : t ≠ 0) (f : CircleL2 T)
    (hreg : ContDiffAt ℝ n
      (fun a : ℝ => circleL2Translation T ((a*t:ℝ) : AddCircle T) f) 0) :
    ∃ u : CircleSobolevSpace T n,
      circleSobolevCoordinate T n 0 u = f ∧
      ∀ j : Fin (n+1), circleSobolevCoordinate T n j u =
        ((((t⁻¹)^j.val:ℝ):ℂ) • iteratedDeriv j.val
          (fun a : ℝ => circleL2Translation T ((a*t:ℝ) : AddCircle T) f) 0) := by
  let path : ℝ → CircleL2 T :=
    fun a => circleL2Translation T ((a*t:ℝ) : AddCircle T) f
  let J : PiLp 2 (fun _ : Fin (n+1) => CircleL2 T) :=
    WithLp.toLp 2 (fun j => (((t⁻¹)^j.val:ℝ):ℂ) • iteratedDeriv j.val path 0)
  have hcoeff (j : Fin (n+1)) (k : ℤ) :
      fourierCoeff (J j) k = (circleFrequencyFactor T k)^j.val*fourierCoeff f k := by
    let L := translationCoefficient T k
    have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have hcomm : L (iteratedDeriv j.val path 0) =
        iteratedDeriv j.val (fun a => L (path a)) 0 :=
      continuous_linear_map_iterated_deriv (L.restrictScalars ℝ) path n j.val hreg hj
    have hpath : (fun a => L (path a)) =
        fun a : ℝ => fourier k ((a*t:ℝ) : AddCircle T)*fourierCoeff f k := by
      funext a
      exact (translation_coefficient_apply T k (path a)).trans
        (circle_l2_translation_fourier T ((a*t:ℝ) : AddCircle T) f k)
    rw [hpath,iteratedDeriv_mul_const_field,translation_mode_iterated_deriv] at hcomm
    change L (iteratedDeriv j.val path 0) =
      ((((t:ℂ)*circleFrequencyFactor T k)^j.val)*
        fourier k ((0*t:ℝ) : AddCircle T))*fourierCoeff f k at hcomm
    have hzero : fourier k ((0*t:ℝ) : AddCircle T) = 1 := by simp
    rw [hzero,mul_one] at hcomm
    change fourierCoeff (((((t⁻¹)^j.val:ℝ):ℂ)) • iteratedDeriv j.val path 0) k = _
    rw [circle_fourierCoeff_smul,← translation_coefficient_apply T k,hcomm]
    exact cancel_translation_scale t ht (circleFrequencyFactor T k) (fourierCoeff f k) j.val
  have hJ : J ∈ circleSobolevJetSubmodule T n := by
    apply (circle_sobolev_jet_mem_iff T n J).mpr
    intro j
    apply weak_circle_deriv_of_fourier
    intro k
    rw [hcoeff j.succ k,hcoeff j.castSucc k]
    change (circleFrequencyFactor T k)^(j.val+1)*fourierCoeff f k =
      circleFrequencyFactor T k*((circleFrequencyFactor T k)^j.val*fourierCoeff f k)
    rw [pow_succ]
    ring
  let u : CircleSobolevSpace T n := ⟨J,hJ⟩
  refine ⟨u,?_,fun _ => rfl⟩
  apply circle_fourier_ext T
  intro k
  change fourierCoeff (J 0) k = fourierCoeff f k
  rw [hcoeff]
  simp

open Set Filter
open scoped Topology

/-- A differentiable translation family yields a continuous Hn curve on
every closed positive time interval. The estimate uses only its L2-valued
parameter derivatives, and keeps all weak spatial derivatives. -/
theorem circle_continuous_sobolev_of_translation
    (n : ℕ) (f : C(unitInterval,CircleL2 T))
    (g : ℝ → C(unitInterval,CircleL2 T))
    (hg : ContDiffAt ℝ n g 0)
    (htranslate : ∀ᶠ a : ℝ in 𝓝 0, ∀ t : unitInterval,
      g a t = circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T) (f t))
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ v : C(Icc r₀ (1:ℝ),CircleSobolevSpace T n),
      ∀ t : Icc r₀ (1:ℝ),
        circleSobolevCoordinate T n 0 (v t) =
          f ⟨(t:ℝ),(hr₀.trans_le t.property.1).le,t.property.2⟩ ∧
        ‖v t‖^2 ≤ ∑ j : Fin (n+1),
          (((r₀⁻¹)^j.val)*‖iteratedDeriv j.val g 0‖)^2 := by
  let unitTime : Icc r₀ (1:ℝ) → unitInterval := fun t =>
    ⟨(t:ℝ),(hr₀.trans_le t.property.1).le,t.property.2⟩
  have hunit : Continuous unitTime := continuous_subtype_val.subtype_mk _
  have htpos (t : Icc r₀ (1:ℝ)) : 0 < (unitTime t:ℝ) :=
    hr₀.trans_le t.property.1
  let path : unitInterval → ℝ → CircleL2 T := fun t a =>
    circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T) (f t)
  have hpoint (t : unitInterval) : ContDiffAt ℝ n (path t) 0 := by
    let L : C(unitInterval,CircleL2 T) →L[ℝ] CircleL2 T :=
      ContinuousMap.evalCLM ℝ t
    have heq : path t =ᶠ[𝓝 0] (fun a => L (g a)) := by
      filter_upwards [htranslate] with a ha
      exact (ha t).symm
    exact (L.contDiff.contDiffAt.comp 0 hg).congr_of_eventuallyEq heq
  have hderiv (t : unitInterval) (j : Fin (n+1)) :
      iteratedDeriv j.val (path t) 0 = (iteratedDeriv j.val g 0) t := by
    let L : C(unitInterval,CircleL2 T) →L[ℝ] CircleL2 T :=
      ContinuousMap.evalCLM ℝ t
    have heq : path t =ᶠ[𝓝 0] (fun a => L (g a)) := by
      filter_upwards [htranslate] with a ha
      exact (ha t).symm
    exact (Filter.EventuallyEq.iteratedDeriv_eq j.val heq).trans
      (continuous_linear_map_iterated_deriv L g n j.val hg
        (Nat.le_of_lt_succ j.isLt)).symm
  let J : Icc r₀ (1:ℝ) → PiLp 2 (fun _ : Fin (n+1) => CircleL2 T) := fun t =>
    WithLp.toLp 2 (fun j => (((((unitTime t:ℝ)⁻¹)^j.val:ℝ):ℂ) •
      (iteratedDeriv j.val g 0) (unitTime t)))
  have hjet (t : Icc r₀ (1:ℝ)) :
      ∃ u : CircleSobolevSpace T n,
        circleSobolevCoordinate T n 0 u = f (unitTime t) ∧
          (u : PiLp 2 (fun _ : Fin (n+1) => CircleL2 T)) = J t := by
    obtain ⟨u,hu,hcoord⟩ := circle_sobolev_of_translation_contDiffAt T n
      (unitTime t:ℝ) (ne_of_gt (htpos t)) (f (unitTime t)) (hpoint (unitTime t))
    refine ⟨u,hu,?_⟩
    apply PiLp.ext
    intro j
    exact (hcoord j).trans (congrArg
      (fun z : CircleL2 T => (((((unitTime t:ℝ)⁻¹)^j.val:ℝ):ℂ) • z))
        (hderiv (unitTime t) j))
  have hmem (t : Icc r₀ (1:ℝ)) : J t ∈ circleSobolevJetSubmodule T n := by
    obtain ⟨u,_,hu⟩ := hjet t
    exact hu ▸ u.property
  have hJ : Continuous J := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => CircleL2 T)).comp
    apply continuous_pi
    intro j
    have hinv : Continuous (fun t : Icc r₀ (1:ℝ) => (unitTime t:ℝ)⁻¹) :=
      (continuous_subtype_val.comp hunit).inv₀ (fun t => ne_of_gt (htpos t))
    exact (Complex.continuous_ofReal.comp (hinv.pow j.val)).smul
      ((iteratedDeriv j.val g 0).continuous.comp hunit)
  let v : C(Icc r₀ (1:ℝ),CircleSobolevSpace T n) :=
    ⟨fun t => ⟨J t,hmem t⟩,hJ.subtype_mk _⟩
  refine ⟨v,?_⟩
  intro t
  have hvalue : circleSobolevCoordinate T n 0 (v t) = f (unitTime t) := by
    obtain ⟨u,hu,hJu⟩ := hjet t
    have hv : v t = u := Subtype.ext hJu.symm
    exact (congrArg (circleSobolevCoordinate T n 0) hv).trans hu
  refine ⟨hvalue,?_⟩
  rw [circle_sobolev_norm_sq T n]
  apply Finset.sum_le_sum
  intro j _
  have hinv : (unitTime t:ℝ)⁻¹ ≤ r₀⁻¹ :=
    (inv_le_inv₀ (htpos t) hr₀).2 t.property.1
  have hpow : ((unitTime t:ℝ)⁻¹)^j.val ≤ (r₀⁻¹)^j.val :=
    pow_le_pow_left₀ (inv_nonneg.mpr (htpos t).le) hinv j.val
  have hn : ‖circleSobolevCoordinate T n j (v t)‖ ≤
      ((r₀⁻¹)^j.val)*‖iteratedDeriv j.val g 0‖ := by
    change ‖((((unitTime t:ℝ)⁻¹)^j.val:ℝ):ℂ) •
      (iteratedDeriv j.val g 0) (unitTime t)‖ ≤ _
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (htpos t).le) j.val)]
    exact mul_le_mul hpow ((iteratedDeriv j.val g 0).norm_coe_le_norm (unitTime t))
      (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr hr₀.le) j.val)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hr₀.le) j.val) (norm_nonneg _))).2 hn

end Lemniscate
