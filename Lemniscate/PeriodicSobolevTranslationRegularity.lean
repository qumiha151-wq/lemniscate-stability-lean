import Lemniscate.PeriodicSobolevTranslation
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

private theorem clm_iterated_deriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (g : ℝ → E) (n i : ℕ)
    (hg : ContDiffAt ℝ n g 0) (hi : i ≤ n) :
    L (iteratedDeriv i g 0) = iteratedDeriv i (fun a => L (g a)) 0 := by
  unfold iteratedDeriv
  change L ((iteratedFDeriv ℝ i g 0) (fun _ => 1)) =
    (iteratedFDeriv ℝ i (L ∘ g) 0) (fun _ => 1)
  rw [L.iteratedFDeriv_comp_left hg (by exact_mod_cast hi)]
  rfl

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
      clm_iterated_deriv (L.restrictScalars ℝ) path n j.val hreg hj
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

end Lemniscate
