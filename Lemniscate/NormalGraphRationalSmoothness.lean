import Lemniscate.NormalGraphPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.AddCircle.Real

/-! Smooth normal-graph coefficients in the Banach algebra of continuous
complex-valued functions on a circle. The fourth height derivative is set to
zero in the lower-order coefficient. Its L2 contribution is separate from
this coefficient theorem and is handled by the quasilinear split.
-/
noncomputable section
namespace Lemniscate

variable (T : ℝ) [Fact (0 < T)]

def normalGraphCoefficientDomain (K : BackgroundJetOver C(AddCircle T, ℂ)) :
    Set (Fin 4 → C(AddCircle T, ℂ)) :=
  {z | IsUnit (graphA K ⟨z 0,z 1,z 2,z 3,0⟩) ∧
    IsUnit (graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩)}

def normalGraphPrincipalCoefficient (K : BackgroundJetOver C(AddCircle T, ℂ))
    (z : Fin 4 → C(AddCircle T, ℂ)) : C(AddCircle T, ℂ) :=
  -((Ring.inverse (graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩))^2)

def normalGraphLowerOrderCoefficient (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) (z : Fin 4 → C(AddCircle T, ℂ)) : C(AddCircle T, ℂ) :=
  normalGraphRationalFlow K c ⟨z 0,z 1,z 2,z 3,0⟩

/-- A common open neighborhood of zero on which the principal and lower-order
coefficients are jointly smooth. Only the first four height coordinates are
continuous functions; no continuity assumption on the fourth derivative is
introduced here. -/
theorem normal_graph_coefficients_smooth (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) :
    IsOpen (normalGraphCoefficientDomain T K) ∧
      (0 : Fin 4 → C(AddCircle T, ℂ)) ∈ normalGraphCoefficientDomain T K ∧
      ∀ z ∈ normalGraphCoefficientDomain T K,
        ContDiffAt ℂ (⊤ : WithTop ℕ∞)
          (fun w : Fin 4 → C(AddCircle T, ℂ) =>
            (normalGraphPrincipalCoefficient T K w,
              normalGraphLowerOrderCoefficient T K c w)) z := by
  have hA : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : Fin 4 → C(AddCircle T, ℂ) => graphA K ⟨z 0,z 1,z 2,z 3,0⟩) := by
    dsimp only [graphA]
    fun_prop
  have hH : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : Fin 4 → C(AddCircle T, ℂ) =>
        graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩) := by
    dsimp only [graphMetricSquared,graphA]
    fun_prop
  have hopen : IsOpen (normalGraphCoefficientDomain T K) := by
    change IsOpen
      ((fun z : Fin 4 → C(AddCircle T, ℂ) => graphA K ⟨z 0,z 1,z 2,z 3,0⟩) ⁻¹'
          {a | IsUnit a} ∩
        (fun z : Fin 4 → C(AddCircle T, ℂ) =>
          graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩) ⁻¹' {a | IsUnit a})
    exact (Units.isOpen.preimage hA.continuous).inter
      (Units.isOpen.preimage hH.continuous)
  have hzero : (0 : Fin 4 → C(AddCircle T, ℂ)) ∈ normalGraphCoefficientDomain T K := by
    change IsUnit (graphA K ⟨0,0,0,0,0⟩) ∧
      IsUnit (graphMetricSquared K ⟨0,0,0,0,0⟩)
    simp [graphA,graphMetricSquared]
  refine ⟨hopen,hzero,?_⟩
  intro z hz
  have huA : IsUnit (graphA K ⟨z 0,z 1,z 2,z 3,0⟩) := hz.1
  have huH : IsUnit (graphMetricSquared K ⟨z 0,z 1,z 2,z 3,0⟩) := hz.2
  have hiA : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun w : Fin 4 → C(AddCircle T, ℂ) =>
        Ring.inverse (graphA K ⟨w 0,w 1,w 2,w 3,0⟩)) z := by
    have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) huA.unit
    rw [huA.unit_spec] at hi
    exact hi.comp z hA.contDiffAt
  have hiH : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun w : Fin 4 → C(AddCircle T, ℂ) =>
        Ring.inverse (graphMetricSquared K ⟨w 0,w 1,w 2,w 3,0⟩)) z := by
    have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) huH.unit
    rw [huH.unit_spec] at hi
    exact hi.comp z hH.contDiffAt
  have hprincipal : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (normalGraphPrincipalCoefficient T K) z := by
    exact (hiH.pow 2).neg
  have hlower : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (normalGraphLowerOrderCoefficient T K c) z := by
    have hAat := hA.contDiffAt (x := z)
    change ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun w : Fin 4 → C(AddCircle T, ℂ) =>
        normalGraphRationalFlow K c ⟨w 0,w 1,w 2,w 3,0⟩) z
    dsimp only [normalGraphRationalFlow,graphCurvatureNumeratorSS,
      graphCurvatureNumeratorS,graphCurvatureNumerator,graphMetricSquaredS,
      graphMetricSquaredSS,graphAs,graphAss,graphSupportNumerator]
    fun_prop
  exact hprincipal.prodMk hlower

end Lemniscate
