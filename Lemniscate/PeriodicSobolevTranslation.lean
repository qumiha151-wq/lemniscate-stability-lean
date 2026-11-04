import Lemniscate.PeriodicSobolevSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral

/-! Spatial translation on the complete periodic Sobolev scale. Every weak
derivative coordinate is the actual Haar-measure pullback x ↦ x+a. Its
inverse is translation by -a. Strong continuity uses the library theorem
for continuous measure-preserving pullbacks, with no finite-mode reduction.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter AddCircle
open scoped ENNReal BigOperators Topology

variable (T : ℝ) [Fact (0 < T)]

/-- Actual right-translation pullback on periodic L2. -/
def circleL2Translation (a : AddCircle T) : CircleL2 T →ₗᵢ[ℂ] CircleL2 T :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : AddCircle T => x+a)
    (measurePreserving_add_right AddCircle.haarAddCircle a)

theorem circle_l2_translation_ae (a : AddCircle T) (f : CircleL2 T) :
    (circleL2Translation T a f : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun x => f (x+a) :=
  Lp.coeFn_compMeasurePreserving f
    (measurePreserving_add_right AddCircle.haarAddCircle a)

private theorem fourier_add_arguments (n : ℤ) (x a : AddCircle T) :
    fourier n (x+a) = fourier n x*fourier n a := by
  simp only [fourier_apply,smul_add,toCircle_add,Circle.coe_mul]

private theorem fourier_neg_arguments (n : ℤ) (a : AddCircle T) :
    fourier (-n) (-a) = fourier n a := by
  simp only [fourier_apply,smul_neg,neg_smul,neg_neg]

theorem circle_l2_translation_fourier (a : AddCircle T) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleL2Translation T a f) n = fourier n a*fourierCoeff f n := by
  have hchar (x : AddCircle T) : fourier (-n) (x-a) = fourier n a*fourier (-n) x := by
    rw [sub_eq_add_neg,fourier_add_arguments,fourier_neg_arguments,mul_comm]
  calc
    fourierCoeff (circleL2Translation T a f) n =
        ∫ x : AddCircle T, fourier (-n) x*f (x+a) ∂AddCircle.haarAddCircle := by
      unfold fourierCoeff
      apply integral_congr_ae
      filter_upwards [circle_l2_translation_ae T a f] with x hx
      simp only [smul_eq_mul,hx]
    _ = ∫ x : AddCircle T, fourier (-n) (x-a)*f x ∂AddCircle.haarAddCircle := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
          (fun x : AddCircle T => fourier (-n) (x-a)*f x) a
    _ = ∫ x : AddCircle T, fourier n a*(fourier (-n) x*f x) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [hchar]
        ring
    _ = fourier n a*fourierCoeff f n := by
      rw [integral_const_mul]
      rfl

private theorem circle_l2_translation_zero (f : CircleL2 T) :
    circleL2Translation T 0 f = f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_l2_translation_fourier,fourier_eval_zero,one_mul]

private theorem circle_l2_translation_add (a b : AddCircle T) (f : CircleL2 T) :
    circleL2Translation T a (circleL2Translation T b f) = circleL2Translation T (a+b) f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_l2_translation_fourier,circle_l2_translation_fourier,
    circle_l2_translation_fourier,fourier_add_arguments]
  ring

private theorem circle_l2_translation_weak_deriv (a : AddCircle T) (f g : CircleL2 T)
    (hfg : HasWeakCircleDeriv T f g) :
    HasWeakCircleDeriv T (circleL2Translation T a f) (circleL2Translation T a g) := by
  apply weak_circle_deriv_of_fourier
  intro n
  rw [circle_l2_translation_fourier,circle_l2_translation_fourier,
    fourier_of_weak_circle_deriv T f g hfg n]
  ring

private theorem circle_l2_translation_continuous (f : CircleL2 T) :
    Continuous (fun a : AddCircle T => circleL2Translation T a f) := by
  let C : C(AddCircle T, C(AddCircle T, AddCircle T)) :=
    (⟨fun p : AddCircle T × AddCircle T => p.2+p.1,
      continuous_snd.add continuous_fst⟩ : C(AddCircle T × AddCircle T, AddCircle T)).curry
  have hc : Continuous (fun a : AddCircle T =>
      Lp.compMeasurePreserving (C a)
        (measurePreserving_add_right AddCircle.haarAddCircle a) f) :=
    (continuous_const : Continuous (fun _ : AddCircle T => f)).compMeasurePreservingLp
      C.continuous (fun a => measurePreserving_add_right AddCircle.haarAddCircle a)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  exact hc

private def circleSobolevTranslationValue (m : ℕ) (a : AddCircle T)
    (f : CircleSobolevSpace T m) : CircleSobolevSpace T m :=
  ⟨WithLp.toLp 2 (fun j : Fin (m+1) =>
      circleL2Translation T a (circleSobolevCoordinate T m j f)),by
    apply (circle_sobolev_jet_mem_iff T m _).mpr
    intro j
    exact circle_l2_translation_weak_deriv T a _ _ (circle_sobolev_weak_deriv T m f j)⟩

private theorem circle_sobolev_translation_value_coordinate (m : ℕ) (a : AddCircle T)
    (f : CircleSobolevSpace T m) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevTranslationValue T m a f) =
      circleL2Translation T a (circleSobolevCoordinate T m j f) := rfl

private theorem circle_sobolev_translation_value_zero (m : ℕ) (f : CircleSobolevSpace T m) :
    circleSobolevTranslationValue T m 0 f = f := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  exact circle_l2_translation_zero T (circleSobolevCoordinate T m j f)

private theorem circle_sobolev_translation_value_add (m : ℕ) (a b : AddCircle T)
    (f : CircleSobolevSpace T m) :
    circleSobolevTranslationValue T m a (circleSobolevTranslationValue T m b f) =
      circleSobolevTranslationValue T m (a+b) f := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  exact circle_l2_translation_add T a b (circleSobolevCoordinate T m j f)

private theorem circle_sobolev_translation_value_norm (m : ℕ) (a : AddCircle T)
    (f : CircleSobolevSpace T m) : ‖circleSobolevTranslationValue T m a f‖ = ‖f‖ := by
  have hs : ‖circleSobolevTranslationValue T m a f‖^2 = ‖f‖^2 := by
    rw [circle_sobolev_norm_sq,circle_sobolev_norm_sq]
    apply Finset.sum_congr rfl
    intro j _
    rw [circle_sobolev_translation_value_coordinate,(circleL2Translation T a).norm_map]
  exact le_antisymm
    ((sq_le_sq₀ (norm_nonneg (circleSobolevTranslationValue T m a f)) (norm_nonneg f)).mp hs.le)
    ((sq_le_sq₀ (norm_nonneg f) (norm_nonneg (circleSobolevTranslationValue T m a f))).mp hs.symm.le)

/-- Translation of every weak derivative jet is a complex linear isometric
equivalence of the complete periodic Sobolev space, in its genuine Hm norm. -/
def circleSobolevTranslation (m : ℕ) (a : AddCircle T) :
    CircleSobolevSpace T m ≃ₗᵢ[ℂ] CircleSobolevSpace T m where
  toFun := circleSobolevTranslationValue T m a
  invFun := circleSobolevTranslationValue T m (-a)
  left_inv f := by
    rw [circle_sobolev_translation_value_add,neg_add_cancel,circle_sobolev_translation_value_zero]
  right_inv f := by
    rw [circle_sobolev_translation_value_add,add_neg_cancel,circle_sobolev_translation_value_zero]
  map_add' f g := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    exact (circleL2Translation T a).map_add (f.1 j) (g.1 j)
  map_smul' c f := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    exact (circleL2Translation T a).map_smul c (f.1 j)
  norm_map' := circle_sobolev_translation_value_norm T m a

/-- Each coordinate is the actual L2 pullback by x ↦ x+a. -/
@[simp] theorem circle_sobolev_translation_coordinate (m : ℕ) (a : AddCircle T)
    (f : CircleSobolevSpace T m) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevTranslation T m a f) =
      Lp.compMeasurePreserving (fun x : AddCircle T => x+a)
        (measurePreserving_add_right AddCircle.haarAddCircle a) (circleSobolevCoordinate T m j f) := rfl

@[simp] theorem circle_sobolev_translation_symm (m : ℕ) (a : AddCircle T) :
    (circleSobolevTranslation T m a).symm = circleSobolevTranslation T m (-a) := by
  ext f
  rfl

theorem circle_sobolev_translation_add (m : ℕ) (a b : AddCircle T)
    (f : CircleSobolevSpace T m) :
    circleSobolevTranslation T m a (circleSobolevTranslation T m b f) =
      circleSobolevTranslation T m (a+b) f :=
  circle_sobolev_translation_value_add T m a b f

/-- Strong continuity in the real translation parameter for every Hm datum. -/
theorem circle_sobolev_translation_continuous (m : ℕ) (f : CircleSobolevSpace T m) :
    Continuous (fun r : ℝ => circleSobolevTranslation T m (r : AddCircle T) f) := by
  have hpi : Continuous (fun a : AddCircle T => fun j : Fin (m+1) =>
      circleL2Translation T a (circleSobolevCoordinate T m j f)) :=
    continuous_pi fun j => circle_l2_translation_continuous T (circleSobolevCoordinate T m j f)
  have hjet : Continuous (fun r : ℝ => WithLp.toLp 2 (fun j : Fin (m+1) =>
      circleL2Translation T (r : AddCircle T) (circleSobolevCoordinate T m j f))) :=
    ((PiLp.continuous_toLp 2 (fun _ : Fin (m+1) => CircleL2 T)).comp hpi).comp
      (AddCircle.continuous_mk' T)
  apply continuous_iff_continuousAt.mpr
  intro r
  apply tendsto_subtype_rng.mpr
  exact hjet.continuousAt

end Lemniscate
