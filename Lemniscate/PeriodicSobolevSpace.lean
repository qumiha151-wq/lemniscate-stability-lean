import Lemniscate.PeriodicH4Domain
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! Complete integer-order periodic Sobolev spaces.

An element consists of its successive weak derivatives in a closed subspace
of a finite L2 Hilbert product. The inherited norm is the square root of the
sum of the squared derivative norms, not the L2 norm on the old H4 submodule.
The circle coordinate has period T and its Haar measure has mass one.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

private abbrev SobolevJetAmbient (m : ℕ) :=
  PiLp 2 (fun _ : Fin (m+1) => CircleL2 T)

private def circleL2Coefficient (n : ℤ) : CircleL2 T →L[ℂ] ℂ :=
  innerSL ℂ (fourierBasis (T := T) n)

private theorem circle_l2_coefficient_apply (n : ℤ) (f : CircleL2 T) :
    circleL2Coefficient T n f = fourierCoeff f n := by
  change inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

private def circleSobolevJetConstraint (m : ℕ) (j : Fin m) (n : ℤ) :
    SobolevJetAmbient T m →L[ℂ] ℂ :=
  (circleL2Coefficient T n).comp
      (PiLp.proj 2 (fun _ : Fin (m+1) => CircleL2 T) j.succ)-
    circleFrequencyFactor T n •
      ((circleL2Coefficient T n).comp
        (PiLp.proj 2 (fun _ : Fin (m+1) => CircleL2 T) j.castSucc))

def circleSobolevJetSubmodule (m : ℕ) : Submodule ℂ (SobolevJetAmbient T m) :=
  ⨅ j : Fin m, ⨅ n : ℤ, (circleSobolevJetConstraint T m j n).ker

theorem circle_sobolev_jet_mem_iff (m : ℕ) (J : SobolevJetAmbient T m) :
    J ∈ circleSobolevJetSubmodule T m ↔
      ∀ j : Fin m, HasWeakCircleDeriv T (J j.castSucc) (J j.succ) := by
  simp only [circleSobolevJetSubmodule,Submodule.mem_iInf]
  change (∀ j : Fin m, ∀ n : ℤ, circleSobolevJetConstraint T m j n J = 0) ↔ _
  constructor
  · intro h j
    apply (weak_circle_deriv_iff_fourier T (J j.castSucc) (J j.succ)).mpr
    intro n
    have hj := h j n
    change circleL2Coefficient T n (J j.succ)-
      circleFrequencyFactor T n*circleL2Coefficient T n (J j.castSucc) = 0 at hj
    rw [circle_l2_coefficient_apply,circle_l2_coefficient_apply,sub_eq_zero] at hj
    exact hj
  · intro h j n
    change circleL2Coefficient T n (J j.succ)-
      circleFrequencyFactor T n*circleL2Coefficient T n (J j.castSucc) = 0
    rw [circle_l2_coefficient_apply,circle_l2_coefficient_apply]
    exact sub_eq_zero.mpr (fourier_of_weak_circle_deriv T _ _ (h j) n)

instance circleSobolevJetSubmodule_isClosed (m : ℕ) :
    IsClosed (circleSobolevJetSubmodule T m : Set (SobolevJetAmbient T m)) := by
  simp only [circleSobolevJetSubmodule,Submodule.coe_iInf]
  exact isClosed_iInter fun j => isClosed_iInter fun n =>
    (circleSobolevJetConstraint T m j n).isClosed_ker

/-- The derivative-jet realization of periodic H^m, with its Hilbert norm. -/
abbrev CircleSobolevSpace (m : ℕ) := circleSobolevJetSubmodule T m

/- NormedAddCommGroup and InnerProductSpace are inherited from the Hilbert
product. Completeness uses the proved closedness, not completeness of the old
H4 domain with its weaker inherited L2 norm. -/
instance circleSobolevSpace_completeSpace (m : ℕ) :
    CompleteSpace (CircleSobolevSpace T m) := inferInstance

/-- Coordinate j is the weak derivative of order j; coordinate 0 is the value. -/
def circleSobolevCoordinate (m : ℕ) (j : Fin (m+1)) :
    CircleSobolevSpace T m →L[ℂ] CircleL2 T :=
  (PiLp.proj 2 (fun _ : Fin (m+1) => CircleL2 T) j).comp
    (circleSobolevJetSubmodule T m).subtypeL

@[simp] theorem circle_sobolev_coordinate_apply (m : ℕ) (j : Fin (m+1))
    (f : CircleSobolevSpace T m) :
    circleSobolevCoordinate T m j f = (f : SobolevJetAmbient T m) j := rfl

theorem circle_sobolev_weak_deriv (m : ℕ) (f : CircleSobolevSpace T m) (j : Fin m) :
    HasWeakCircleDeriv T ((f : SobolevJetAmbient T m) j.castSucc)
      ((f : SobolevJetAmbient T m) j.succ) :=
  (circle_sobolev_jet_mem_iff T m (f : SobolevJetAmbient T m)).mp f.property j

theorem circle_sobolev_norm_sq (m : ℕ) (f : CircleSobolevSpace T m) :
    ‖f‖^2 = ∑ j : Fin (m+1), ‖circleSobolevCoordinate T m j f‖^2 := by
  change ‖(f : SobolevJetAmbient T m)‖^2 =
    ∑ j : Fin (m+1), ‖(f : SobolevJetAmbient T m) j‖^2
  exact PiLp.norm_sq_eq_of_L2 _ _

theorem circle_sobolev_coordinate_norm_le (m : ℕ) (j : Fin (m+1)) :
    ‖circleSobolevCoordinate T m j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 1)
  intro f
  change ‖(f : SobolevJetAmbient T m) j‖ ≤ 1*‖(f : SobolevJetAmbient T m)‖
  simpa only [one_mul] using PiLp.norm_apply_le (f : SobolevJetAmbient T m) j

theorem circle_sobolev_value_injective (m : ℕ) :
    Function.Injective (circleSobolevCoordinate T m 0) := by
  intro f g h0
  change (f : SobolevJetAmbient T m) 0 = (g : SobolevJetAmbient T m) 0 at h0
  apply Subtype.ext
  apply PiLp.ext
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ j hj =>
      have hf := circle_sobolev_weak_deriv T m f j
      have hg := circle_sobolev_weak_deriv T m g j
      rw [← hj] at hg
      exact weak_circle_deriv_unique T _ _ _ hf hg

theorem circle_sobolev_two_range (f : CircleL2 T) :
    (∃ u : CircleSobolevSpace T 2, circleSobolevCoordinate T 2 0 u = f) ↔
      InCircleH2 T f := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨circleSobolevCoordinate T 2 1 u,circleSobolevCoordinate T 2 2 u,
      circle_sobolev_weak_deriv T 2 u 0,circle_sobolev_weak_deriv T 2 u 1⟩
  · rintro ⟨f₁,f₂,hf,hf₁⟩
    let J : SobolevJetAmbient T 2 := WithLp.toLp 2 ![f,f₁,f₂]
    have hJ : J ∈ circleSobolevJetSubmodule T 2 := by
      apply (circle_sobolev_jet_mem_iff T 2 J).mpr
      intro j
      fin_cases j
      · exact hf
      · exact hf₁
    exact ⟨⟨J,hJ⟩,rfl⟩

theorem circle_sobolev_four_range (f : CircleL2 T) :
    (∃ u : CircleSobolevSpace T 4, circleSobolevCoordinate T 4 0 u = f) ↔
      InCircleH4 T f := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨circleSobolevCoordinate T 4 1 u,circleSobolevCoordinate T 4 2 u,
      circleSobolevCoordinate T 4 3 u,circleSobolevCoordinate T 4 4 u,
      circle_sobolev_weak_deriv T 4 u 0,circle_sobolev_weak_deriv T 4 u 1,
      circle_sobolev_weak_deriv T 4 u 2,circle_sobolev_weak_deriv T 4 u 3⟩
  · rintro ⟨f₁,f₂,f₃,f₄,hf,hf₁,hf₂,hf₃⟩
    let J : SobolevJetAmbient T 4 := WithLp.toLp 2 ![f,f₁,f₂,f₃,f₄]
    have hJ : J ∈ circleSobolevJetSubmodule T 4 := by
      apply (circle_sobolev_jet_mem_iff T 4 J).mpr
      intro j
      fin_cases j
      · exact hf
      · exact hf₁
      · exact hf₂
      · exact hf₃
    exact ⟨⟨J,hJ⟩,rfl⟩

end Lemniscate
