import Lemniscate.PeriodicSobolevDerivatives
import Lemniscate.PeriodicSobolevConjugation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! All continuous classical derivatives of an integer-order Sobolev element.
Each representative uses only one adjacent H1 block of its actual weak jet.
The resulting finite jet is a bounded linear map, so it also preserves
continuity of time-dependent Sobolev data.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ContDiff

variable (T : ℝ) [Fact (0 < T)]

private def circleSobolevAdjacentLinear (m : ℕ) (j : Fin (m+1)) :
    CircleSobolevSpace T (m+1) →ₗ[ℂ] CircleSobolevSpace T 1 where
  toFun f :=
    ⟨WithLp.toLp 2 ![circleSobolevCoordinate T (m+1) j.castSucc f,
      circleSobolevCoordinate T (m+1) j.succ f],by
      apply (circle_sobolev_jet_mem_iff T 1 _).mpr
      intro i
      fin_cases i
      exact circle_sobolev_weak_deriv T (m+1) f j⟩
  map_add' f g := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  map_smul' c f := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl

private theorem circle_sobolev_adjacent_norm_le (m : ℕ) (j : Fin (m+1))
    (f : CircleSobolevSpace T (m+1)) :
    ‖circleSobolevAdjacentLinear T m j f‖ ≤ 2*‖f‖ := by
  have hcoord (i : Fin ((m+1)+1)) :
      ‖circleSobolevCoordinate T (m+1) i f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using (circleSobolevCoordinate T (m+1) i).le_of_opNorm_le
      (circle_sobolev_coordinate_norm_le T (m+1) i) f
  have hs : ‖circleSobolevAdjacentLinear T m j f‖^2 =
      ‖circleSobolevCoordinate T (m+1) j.castSucc f‖^2+
        ‖circleSobolevCoordinate T (m+1) j.succ f‖^2 := by
    rw [circle_sobolev_norm_sq,Fin.sum_univ_two]
    rfl
  have h₀ := (sq_le_sq₀ (norm_nonneg _)
    (norm_nonneg f)).2 (hcoord j.castSucc)
  have h₁ := (sq_le_sq₀ (norm_nonneg _)
    (norm_nonneg f)).2 (hcoord j.succ)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*‖f‖)).1
  nlinarith [sq_nonneg ‖f‖]

private def circleSobolevAdjacent (m : ℕ) (j : Fin (m+1)) :
    CircleSobolevSpace T (m+1) →L[ℂ] CircleSobolevSpace T 1 :=
  (circleSobolevAdjacentLinear T m j).mkContinuous 2
    (circle_sobolev_adjacent_norm_le T m j)

/-- The continuous representatives of derivatives zero through m of H^(m+1).
The finite family carries its usual maximum norm. -/
def circleSobolevClassicalJet (m : ℕ) :
    CircleSobolevSpace T (m+1) →L[ℂ] (Fin (m+1) → C(AddCircle T,ℂ)) :=
  ContinuousLinearMap.pi fun j =>
    (circleSobolevH1Embedding T).comp (circleSobolevAdjacent T m j)

theorem circle_sobolev_classical_jet_l2 (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) (j : Fin (m+1)) :
    circleContinuousL2 T (circleSobolevClassicalJet T m f j) =
      circleSobolevCoordinate T (m+1) j.castSucc f := by
  change circleContinuousL2 T
    (circleSobolevH1Embedding T (circleSobolevAdjacent T m j f)) = _
  rw [circle_sobolev_h1_embedding_l2]
  rfl

theorem circle_sobolev_classical_jet_deriv (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) (j : Fin m) :
    HasCircleDeriv T (circleSobolevClassicalJet T m f j.castSucc)
      (circleSobolevClassicalJet T m f j.succ) := by
  apply circle_classical_deriv_of_continuous_weak T
  rw [circle_sobolev_classical_jet_l2,circle_sobolev_classical_jet_l2]
  simpa only [circle_sobolev_coordinate_apply,Fin.castSucc_succ] using
    circle_sobolev_weak_deriv T (m+1) f j.castSucc

theorem circle_sobolev_classical_jet_conjugation (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) (j : Fin (m+1)) :
    circleSobolevClassicalJet T m (circleSobolevConjugation T (m+1) f) j =
      star (circleSobolevClassicalJet T m f j) := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T
      (circleSobolevClassicalJet T m (circleSobolevConjugation T (m+1) f) j) =
    circleContinuousL2 T (star (circleSobolevClassicalJet T m f j))
  rw [circle_sobolev_classical_jet_l2,circle_continuous_l2_star,
    circle_sobolev_conjugation_coordinate,circle_sobolev_classical_jet_l2]

theorem circle_sobolev_classical_jet_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : CircleSobolevSpace T (m+1),
      ‖circleSobolevClassicalJet T m f‖ ≤ C*‖f‖ := by
  refine ⟨‖circleSobolevClassicalJet T m‖+1,by positivity,fun f => ?_⟩
  exact ((circleSobolevClassicalJet T m).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)) (norm_nonneg f))

private theorem finite_circle_derivative_chain_contDiff
    (m : ℕ) (D : Fin (m+1) → C(AddCircle T,ℂ))
    (hD : ∀ j : Fin m, HasCircleDeriv T (D j.castSucc) (D j.succ)) :
    ContDiff ℝ (m : ℕ∞ω) (fun x : ℝ => D 0 (x : AddCircle T)) := by
  induction m with
  | zero =>
      exact contDiff_zero.mpr ((D 0).continuous.comp (AddCircle.continuous_mk' T))
  | succ m ih =>
      let E : Fin (m+1) → C(AddCircle T,ℂ) := fun j => D j.succ
      have hE (j : Fin m) : HasCircleDeriv T (E j.castSucc) (E j.succ) := by
        simpa only [E,Fin.castSucc_succ] using hD j.succ
      have hd : deriv (fun x : ℝ => D 0 (x : AddCircle T)) =
          fun x : ℝ => E 0 (x : AddCircle T) := by
        funext x
        exact (hD 0 x).deriv
      have hc : ContDiff ℝ (m : ℕ∞ω)
          (deriv (fun x : ℝ => D 0 (x : AddCircle T))) := by
        rw [hd]
        exact ih E hE
      have hs := (contDiff_succ_iff_deriv (n := (m : ℕ∞ω))).mpr
        ⟨fun x => (hD 0 x).differentiableAt,by simp,hc⟩
      simpa only [Nat.cast_add,Nat.cast_one] using! hs

/-- The bounded continuous jet is the actual classical jet of the periodic
lift, which is C^m. The last Sobolev coordinate remains an L2 derivative. -/
theorem circle_sobolev_classical_regularity (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) :
    let D := circleSobolevClassicalJet T m f
    ContDiff ℝ (m : ℕ∞ω) (fun x : ℝ => D 0 (x : AddCircle T)) ∧
      ∀ j : Fin (m+1),
        iteratedDeriv j.val (fun x : ℝ => D 0 (x : AddCircle T)) =
          fun x : ℝ => D j (x : AddCircle T) := by
  let D := circleSobolevClassicalJet T m f
  have hD := circle_sobolev_classical_jet_deriv T m f
  refine ⟨finite_circle_derivative_chain_contDiff T m D hD,?_⟩
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
      change iteratedDeriv (j.val+1) (fun x : ℝ => D 0 (x : AddCircle T)) =
        fun x : ℝ => D j.succ (x : AddCircle T)
      change iteratedDeriv j.val (fun x : ℝ => D 0 (x : AddCircle T)) =
        fun x : ℝ => D j.castSucc (x : AddCircle T) at ih
      rw [iteratedDeriv_succ,ih]
      funext x
      exact (hD j x).deriv

end Lemniscate
