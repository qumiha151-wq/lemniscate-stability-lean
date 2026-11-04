import Lemniscate.NormalGraphLowerPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Shared normal-graph coefficient maps over a complete commutative complex
Banach algebra. Fixed real coefficients act by multiplication with their
images in the algebra. No spatial or time evaluation, Sobolev space, or
pointwise inverse identity is involved. The circle coefficient maps can be
defined by specialization of this common construction. -/
noncomputable section
namespace Lemniscate

section Definitions
variable (R : Type*) [CommRing R] [Algebra ℝ R]

def normalGraphCoefficientDomainOver (K : BackgroundJetOver R) : Set (Fin 4 → R) :=
  {z | IsUnit (graphA K ⟨z 0,z 1,z 2,z 3,0⟩) ∧
    IsUnit (graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩)}

def normalGraphPrincipalCoefficientOver (K : BackgroundJetOver R) (z : Fin 4 → R) : R :=
  -((Ring.inverse (graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩))^2)

def normalGraphLowerOrderCoefficientOver (K : BackgroundJetOver R)
    (c : ℝ) (z : Fin 4 → R) : R :=
  normalGraphRationalFlow K c ⟨z 0,z 1,z 2,z 3,0⟩

private def normalGraphLowerSampleOver (u : Fin 2 → R) (v w : R) : Fin 4 → R :=
  ![u 0,u 1,v,w]

def normalGraphLowerCoefficientDomainOver (K : BackgroundJetOver R) : Set (Fin 2 → R) :=
  (fun u => normalGraphLowerSampleOver R u 0 0) ⁻¹' normalGraphCoefficientDomainOver R K

def normalGraphLowerCoefficientMapOver (K : BackgroundJetOver R) (c : ℝ)
    (u : Fin 2 → R) : Fin 6 → R :=
  normalGraphLowerCoefficients K c (u 0) (u 1)

end Definitions

section Smoothness
variable (R : Type*) [NormedCommRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    [Algebra ℝ R]

/-- The actual unit domain is open, contains zero, and supports smooth
principal and lower-order rational coefficients in the same Banach algebra. -/
theorem normal_graph_coefficients_smooth_over (K : BackgroundJetOver R) (c : ℝ) :
    IsOpen (normalGraphCoefficientDomainOver R K) ∧
      (0 : Fin 4 → R) ∈ normalGraphCoefficientDomainOver R K ∧
      ∀ z ∈ normalGraphCoefficientDomainOver R K,
        ContDiffAt ℂ (⊤ : WithTop ℕ∞)
          (fun w : Fin 4 → R =>
            (normalGraphPrincipalCoefficientOver R K w,
              normalGraphLowerOrderCoefficientOver R K c w)) z := by
  have hA : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : Fin 4 → R => graphA K ⟨z 0,z 1,z 2,z 3,0⟩) := by
    dsimp only [graphA]
    fun_prop
  have hH : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : Fin 4 → R => graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩) := by
    dsimp only [graphMetricSquared,graphA]
    fun_prop
  have hopen : IsOpen (normalGraphCoefficientDomainOver R K) := by
    change IsOpen
      ((fun z : Fin 4 → R => graphA K ⟨z 0,z 1,z 2,z 3,0⟩) ⁻¹' {a | IsUnit a} ∩
        (fun z : Fin 4 → R => graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩) ⁻¹' {a | IsUnit a})
    exact (Units.isOpen.preimage hA.continuous).inter
      (Units.isOpen.preimage hH.continuous)
  have hzero : (0 : Fin 4 → R) ∈ normalGraphCoefficientDomainOver R K := by
    change IsUnit (graphA K ⟨0,0,0,0,0⟩) ∧ IsUnit (graphMetricSquared K ⟨0,0,0,0,0⟩)
    simp [graphA,graphMetricSquared]
  refine ⟨hopen,hzero,?_⟩
  intro z hz
  have huA : IsUnit (graphA K ⟨z 0,z 1,z 2,z 3,0⟩) := hz.1
  have huH : IsUnit (graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩) := hz.2
  have hiA : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun w : Fin 4 → R => Ring.inverse (graphA K ⟨w 0,w 1,w 2,w 3,0⟩)) z := by
    have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) huA.unit
    rw [huA.unit_spec] at hi
    exact hi.comp z hA.contDiffAt
  have hiH : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun w : Fin 4 → R => Ring.inverse (graphMetricSquared K ⟨w 0,w 1,w 2,w 3,0⟩)) z := by
    have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) huH.unit
    rw [huH.unit_spec] at hi
    exact hi.comp z hH.contDiffAt
  have hprincipal : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (normalGraphPrincipalCoefficientOver R K) z := (hiH.pow 2).neg
  have hlower : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (normalGraphLowerOrderCoefficientOver R K c) z := by
    have hAat := hA.contDiffAt (x := z)
    change ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun w : Fin 4 → R => normalGraphRationalFlow K c ⟨w 0,w 1,w 2,w 3,0⟩) z
    dsimp only [normalGraphRationalFlow,graphCurvatureNumeratorSS,
      graphCurvatureNumeratorS,graphCurvatureNumerator,graphMetricSquaredS,
      graphMetricSquaredSS,graphAs,graphAss,graphSupportNumerator]
    simp only [Algebra.smul_def]
    fun_prop
  exact hprincipal.prodMk hlower

omit [CompleteSpace R] [Algebra ℝ R] in
private theorem normal_graph_lower_sample_contDiff_over (v w : R) :
    ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun u : Fin 2 → R => normalGraphLowerSampleOver R u v w) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [normalGraphLowerSampleOver] <;> fun_prop

set_option maxHeartbeats 800000 in
/-- All six genuine lower-order polynomial coefficients are smooth
functions of height and first derivative on the same actual unit domain. -/
theorem normal_graph_lower_coefficients_smooth_over (K : BackgroundJetOver R) (c : ℝ) :
    IsOpen (normalGraphLowerCoefficientDomainOver R K) ∧
      (0 : Fin 2 → R) ∈ normalGraphLowerCoefficientDomainOver R K ∧
      ∀ u ∈ normalGraphLowerCoefficientDomainOver R K,
        ContDiffAt ℂ (⊤ : WithTop ℕ∞) (normalGraphLowerCoefficientMapOver R K c) u := by
  obtain ⟨hopen,hzero,hsmooth⟩ := normal_graph_coefficients_smooth_over R K c
  have hopen' : IsOpen (normalGraphLowerCoefficientDomainOver R K) :=
    hopen.preimage (normal_graph_lower_sample_contDiff_over R 0 0).continuous
  have hzero' : (0 : Fin 2 → R) ∈ normalGraphLowerCoefficientDomainOver R K := by
    change normalGraphLowerSampleOver R 0 0 0 ∈ normalGraphCoefficientDomainOver R K
    have hs : normalGraphLowerSampleOver R (0 : Fin 2 → R) 0 0 = (0 : Fin 4 → R) := by
      funext i
      fin_cases i <;> rfl
    rw [hs]
    exact hzero
  refine ⟨hopen',hzero',?_⟩
  intro u hu
  have hsample (v w : R) :
      normalGraphLowerSampleOver R u v w ∈ normalGraphCoefficientDomainOver R K := by
    exact hu
  have hb (v w : R) : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : Fin 2 → R => normalGraphRationalFlow K c ⟨y 0,y 1,v,w,0⟩) u := by
    have h := ((hsmooth _ (hsample v w)).snd).comp u
      (normal_graph_lower_sample_contDiff_over R v w).contDiffAt
    simpa only [Function.comp_def,normalGraphLowerOrderCoefficientOver,
      normalGraphLowerSampleOver,Matrix.cons_val_zero,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons] using h
  have hb₀₀ := hb 0 0
  have hb₁₀ := hb 1 0
  have hbm₀ := hb (-1) 0
  have hb₂₀ := hb 2 0
  have hb₀₁ := hb 0 1
  have hb₁₁ := hb 1 1
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp [normalGraphLowerCoefficientMapOver,normalGraphLowerCoefficients,
    Matrix.cons_val_zero,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  all_goals try simp only [Algebra.smul_def]
  all_goals fun_prop

end Smoothness
end Lemniscate
