import Lemniscate.PeriodicSobolevSpace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual continuous representative of a periodic H1 function.

Absolute Fourier convergence follows from the square-summable integer inverse
sequence and the L2 weak derivative. The closed graph theorem supplies the
continuous linear embedding without an unnecessary explicit numerical constant.
Higher continuous derivative representatives are a separate subsequent step.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal Topology

private theorem integer_inverse_coefficients_mem_l2 :
    Memℓp (fun n : ℤ => (n:ℂ)⁻¹) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_inv,Complex.norm_intCast,
    inv_pow,sq_abs,one_div] using
      (Real.summable_one_div_int_pow (p := 2)).mpr (by decide)

variable (T : ℝ) [Fact (0 < T)]

private theorem circle_h1_coefficients_norm_summable (f : CircleSobolevSpace T 1) :
    Summable (fun n : ℤ => ‖fourierCoeff (circleSobolevCoordinate T 1 0 f) n‖) := by
  let u := circleSobolevCoordinate T 1 0 f
  let g := circleSobolevCoordinate T 1 1 f
  have hweak : HasWeakCircleDeriv T u g := circle_sobolev_weak_deriv T 1 f 0
  let a : ℂ := (((2*Real.pi/T:ℝ):ℂ)*I)⁻¹
  let v : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨fun n => a*(n:ℂ)⁻¹,integer_inverse_coefficients_mem_l2.const_mul a⟩
  have hpq : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hs := lp.summable_mul hpq v ((fourierBasis (T := T)).repr g)
  have hT : 0 < T := Fact.out
  have hscale : (((2*Real.pi/T:ℝ):ℂ)*I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : 0 < 2*Real.pi/T))) I_ne_zero
  have heq (n : ℤ) (hn : n ≠ 0) :
      v n*fourierCoeff g n = fourierCoeff u n := by
    rw [fourier_of_weak_circle_deriv T u g hweak n]
    have hω : circleFrequencyFactor T n = (((2*Real.pi/T:ℝ):ℂ)*I)*(n:ℂ) := by
      dsimp only [circleFrequencyFactor]
      push_cast
      ring
    have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have ha : a*(((2*Real.pi/T:ℝ):ℂ)*I) = 1 := inv_mul_cancel₀ hscale
    change (a*(n:ℂ)⁻¹)*(circleFrequencyFactor T n*fourierCoeff u n) = fourierCoeff u n
    rw [hω]
    calc
      (a*(n:ℂ)⁻¹)*(((((2*Real.pi/T:ℝ):ℂ)*I)*(n:ℂ))*fourierCoeff u n) =
          (a*(((2*Real.pi/T:ℝ):ℂ)*I))*(((n:ℂ)⁻¹*(n:ℂ))*fourierCoeff u n) := by ring
      _ = fourierCoeff u n := by rw [ha,inv_mul_cancel₀ hnc,one_mul,one_mul]
  apply hs.congr_cofinite
  refine (eventually_cofinite_ne (0:ℤ)).mono ?_
  intro n hn
  change ‖v n‖*‖((fourierBasis (T := T)).repr g) n‖ = ‖fourierCoeff u n‖
  rw [fourierBasis_repr,← norm_mul,heq n hn]

private def circleH1Representative (f : CircleSobolevSpace T 1) : C(AddCircle T, ℂ) :=
  ∑' n : ℤ, fourierCoeff (circleSobolevCoordinate T 1 0 f) n • fourier (T := T) n

private theorem circle_h1_series_summable (f : CircleSobolevSpace T 1) :
    Summable (fun n : ℤ =>
      fourierCoeff (circleSobolevCoordinate T 1 0 f) n • fourier (T := T) n) := by
  apply Summable.of_norm
  simpa only [norm_smul,fourier_norm,mul_one] using
    circle_h1_coefficients_norm_summable T f

private theorem circle_h1_representative_l2 (f : CircleSobolevSpace T 1) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleH1Representative T f) =
      circleSobolevCoordinate T 1 0 f := by
  have hs : HasSum (fun n : ℤ =>
      fourierCoeff (circleSobolevCoordinate T 1 0 f) n • fourierBasis (T := T) n)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleH1Representative T f)) := by
    convert! (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).hasSum
      (circle_h1_series_summable T f).hasSum using 1
    funext n
    simp only [Function.comp_apply,map_smul]
    change fourierCoeff (circleSobolevCoordinate T 1 0 f) n • fourierBasis (T := T) n =
      fourierCoeff (circleSobolevCoordinate T 1 0 f) n • circleContinuousL2 T (fourier n)
    rw [circle_continuous_l2_fourier_basis]
  have hb : HasSum (fun n : ℤ =>
      fourierCoeff (circleSobolevCoordinate T 1 0 f) n • fourierBasis (T := T) n)
      (circleSobolevCoordinate T 1 0 f) := by
    simpa only [fourierBasis_repr] using
      (fourierBasis (T := T)).hasSum_repr (circleSobolevCoordinate T 1 0 f)
  exact hs.unique hb

private def circleH1RepresentativeLinear :
    CircleSobolevSpace T 1 →ₗ[ℂ] C(AddCircle T, ℂ) where
  toFun := circleH1Representative T
  map_add' f g := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    simp only [map_add,circle_h1_representative_l2]
  map_smul' c f := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    simp only [map_smul,circle_h1_representative_l2,RingHom.id_apply]

private theorem circle_h1_representative_graph_closed :
    IsClosed ((circleH1RepresentativeLinear T).graph :
      Set (CircleSobolevSpace T 1 × C(AddCircle T, ℂ))) := by
  have hgraph : ((circleH1RepresentativeLinear T).graph :
      Set (CircleSobolevSpace T 1 × C(AddCircle T, ℂ))) =
      {p | ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ p.2 =
        circleSobolevCoordinate T 1 0 p.1} := by
    ext p
    change p.2 = circleH1Representative T p.1 ↔
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ p.2 = circleSobolevCoordinate T 1 0 p.1
    constructor
    · intro hp
      rw [hp]
      exact circle_h1_representative_l2 T p.1
    · intro hp
      apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
      change ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ p.2 =
        ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleH1Representative T p.1)
      rw [circle_h1_representative_l2]
      exact hp
  rw [hgraph]
  exact isClosed_eq
    ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).continuous.comp continuous_snd)
    ((circleSobolevCoordinate T 1 0).continuous.comp continuous_fst)

/-- The unique continuous representative of a periodic H1 function, as a CLM. -/
def circleSobolevH1Embedding : CircleSobolevSpace T 1 →L[ℂ] C(AddCircle T, ℂ) :=
  ContinuousLinearMap.ofIsClosedGraph (g := circleH1RepresentativeLinear T)
    (circle_h1_representative_graph_closed T)

theorem circle_sobolev_h1_embedding_l2 (f : CircleSobolevSpace T 1) :
    circleContinuousL2 T (circleSobolevH1Embedding T f) = circleSobolevCoordinate T 1 0 f := by
  exact circle_h1_representative_l2 T f

theorem circle_sobolev_h1_embedding_injective : Function.Injective (circleSobolevH1Embedding T) := by
  intro f g hfg
  apply circle_sobolev_value_injective T 1
  rw [← circle_sobolev_h1_embedding_l2 T f,← circle_sobolev_h1_embedding_l2 T g,hfg]

theorem circle_sobolev_h1_embedding_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ f : CircleSobolevSpace T 1,
      ‖circleSobolevH1Embedding T f‖ ≤ C*‖f‖ := by
  refine ⟨‖circleSobolevH1Embedding T‖+1,by positivity,?_⟩
  intro f
  exact ((circleSobolevH1Embedding T).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))
      (norm_nonneg f))

end Lemniscate
