import Lemniscate.NormalGraphCoefficientAlgebra

/-! Joint smoothness in the background and the lower normal-graph jet.

Background fields are ordinary finite coordinates.  The existing jet
record is only assembled from those coordinates; it receives no additional
norm or topology.  All coefficients are the already defined rational flow
and its six polynomial coefficients.

-/

noncomputable section
namespace Lemniscate

/-- Background coordinates are k, k_s, k_ss, k_sss, eta and b, in this order. -/
def normalGraphBackgroundFromCoordinates {R : Type*} (a : Fin 6 → R) :
    BackgroundJetOver R :=
  ⟨a 0,a 1,a 2,a 3,a 4,a 5⟩

section Definitions
variable (R : Type*) [CommRing R] [Algebra ℝ R]

def normalGraphJointCoefficientDomainOver : Set ((Fin 6 → R) × (Fin 2 → R)) :=
  {x | x.2 ∈ normalGraphLowerCoefficientDomainOver R
    (normalGraphBackgroundFromCoordinates x.1)}

/-- The principal coefficient and the same six lower coefficients, now
viewed jointly as functions of the background and the first two height jets. -/
def normalGraphJointCoefficientMapOver (c : ℝ)
    (x : (Fin 6 → R) × (Fin 2 → R)) : R × (Fin 6 → R) :=
  (normalGraphPrincipalCoefficientOver R (normalGraphBackgroundFromCoordinates x.1)
      ![x.2 0,x.2 1,0,0],
    normalGraphLowerCoefficientMapOver R (normalGraphBackgroundFromCoordinates x.1) c x.2)

end Definitions

section Smoothness
variable (R : Type*) [NormedCommRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    [Algebra ℝ R]

private theorem joint_metric_polynomial_smooth :
    ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun x : (Fin 6 → R) × (Fin 2 → R) =>
        graphA (normalGraphBackgroundFromCoordinates x.1) ⟨x.2 0,x.2 1,0,0,0⟩) ∧
    ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun x : (Fin 6 → R) × (Fin 2 → R) =>
        graphMetricSquared (normalGraphBackgroundFromCoordinates x.1)
          ⟨x.2 0,x.2 1,0,0,0⟩) := by
  constructor
  · dsimp only [graphA,normalGraphBackgroundFromCoordinates]
    fun_prop
  · dsimp only [graphMetricSquared,graphA,normalGraphBackgroundFromCoordinates]
    fun_prop

private theorem joint_inverse_smooth
    (x : (Fin 6 → R) × (Fin 2 → R))
    (hx : x ∈ normalGraphJointCoefficientDomainOver R) :
    ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : (Fin 6 → R) × (Fin 2 → R) =>
        Ring.inverse (graphA (normalGraphBackgroundFromCoordinates y.1)
          ⟨y.2 0,y.2 1,0,0,0⟩)) x ∧
    ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : (Fin 6 → R) × (Fin 2 → R) =>
        Ring.inverse (graphMetricSquared (normalGraphBackgroundFromCoordinates y.1)
          ⟨y.2 0,y.2 1,0,0,0⟩)) x := by
  obtain ⟨hA,hH⟩ := joint_metric_polynomial_smooth R
  change IsUnit (graphA (normalGraphBackgroundFromCoordinates x.1)
      ⟨x.2 0,x.2 1,0,0,0⟩) ∧
    IsUnit (graphMetricSquared (normalGraphBackgroundFromCoordinates x.1)
      ⟨x.2 0,x.2 1,0,0,0⟩) at hx
  constructor
  · have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) hx.1.unit
    rw [hx.1.unit_spec] at hi
    exact hi.comp x hA.contDiffAt
  · have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) hx.2.unit
    rw [hx.2.unit_spec] at hi
    exact hi.comp x hH.contDiffAt

set_option maxHeartbeats 800000 in
private theorem joint_flow_sample_smooth (c : ℝ) (v w : R)
    (x : (Fin 6 → R) × (Fin 2 → R))
    (hx : x ∈ normalGraphJointCoefficientDomainOver R) :
    ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : (Fin 6 → R) × (Fin 2 → R) =>
        normalGraphRationalFlow (normalGraphBackgroundFromCoordinates y.1) c
          ⟨y.2 0,y.2 1,v,w,0⟩) x := by
  obtain ⟨hA,hH⟩ := joint_metric_polynomial_smooth R
  obtain ⟨hiA,hiH⟩ := joint_inverse_smooth R x hx
  have hAat := hA.contDiffAt (x := x)
  have hHat := hH.contDiffAt (x := x)
  dsimp only [normalGraphRationalFlow,graphCurvatureNumeratorSS,
    graphCurvatureNumeratorS,graphCurvatureNumerator,graphMetricSquaredS,
    graphMetricSquaredSS,graphAs,graphAss,graphSupportNumerator,
    normalGraphBackgroundFromCoordinates]
  simp only [Algebra.smul_def]
  fun_prop

set_option maxHeartbeats 800000 in
/-- On the actual unit domain, the principal coefficient and all six
lower coefficients are jointly complex smooth in the background fields
and the first two height jets. Every zero height jet belongs to this domain. -/
theorem normal_graph_joint_coefficients_smooth_over (c : ℝ) :
    IsOpen (normalGraphJointCoefficientDomainOver R) ∧
      (∀ a : Fin 6 → R, (a,(0 : Fin 2 → R)) ∈ normalGraphJointCoefficientDomainOver R) ∧
      ContDiffOn ℂ (⊤ : WithTop ℕ∞) (normalGraphJointCoefficientMapOver R c)
        (normalGraphJointCoefficientDomainOver R) := by
  obtain ⟨hA,hH⟩ := joint_metric_polynomial_smooth R
  have hopen : IsOpen (normalGraphJointCoefficientDomainOver R) := by
    change IsOpen
      ((fun x : (Fin 6 → R) × (Fin 2 → R) =>
        graphA (normalGraphBackgroundFromCoordinates x.1)
          ⟨x.2 0,x.2 1,0,0,0⟩) ⁻¹' {a | IsUnit a} ∩
        (fun x : (Fin 6 → R) × (Fin 2 → R) =>
          graphMetricSquared (normalGraphBackgroundFromCoordinates x.1)
            ⟨x.2 0,x.2 1,0,0,0⟩) ⁻¹' {a | IsUnit a})
    exact (Units.isOpen.preimage hA.continuous).inter
      (Units.isOpen.preimage hH.continuous)
  have hzero (a : Fin 6 → R) :
      (a,(0 : Fin 2 → R)) ∈ normalGraphJointCoefficientDomainOver R := by
    change IsUnit (graphA (normalGraphBackgroundFromCoordinates a) ⟨0,0,0,0,0⟩) ∧
      IsUnit (graphMetricSquared (normalGraphBackgroundFromCoordinates a) ⟨0,0,0,0,0⟩)
    simp [graphA,graphMetricSquared]
  refine ⟨hopen,hzero,?_⟩
  intro x hx
  obtain ⟨hiA,hiH⟩ := joint_inverse_smooth R x hx
  have hprincipal : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : (Fin 6 → R) × (Fin 2 → R) =>
        normalGraphPrincipalCoefficientOver R (normalGraphBackgroundFromCoordinates y.1)
          ![y.2 0,y.2 1,0,0]) x := by
    change ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : (Fin 6 → R) × (Fin 2 → R) =>
        -((Ring.inverse (graphMetricSquared (normalGraphBackgroundFromCoordinates y.1)
          ⟨y.2 0,y.2 1,0,0,0⟩))^2)) x
    exact (hiH.pow 2).neg
  have hb₀₀ := joint_flow_sample_smooth R c 0 0 x hx
  have hb₁₀ := joint_flow_sample_smooth R c 1 0 x hx
  have hbm₀ := joint_flow_sample_smooth R c (-1) 0 x hx
  have hb₂₀ := joint_flow_sample_smooth R c 2 0 x hx
  have hb₀₁ := joint_flow_sample_smooth R c 0 1 x hx
  have hb₁₁ := joint_flow_sample_smooth R c 1 1 x hx
  have hlower : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : (Fin 6 → R) × (Fin 2 → R) =>
        normalGraphLowerCoefficientMapOver R (normalGraphBackgroundFromCoordinates y.1)
          c y.2) x := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> simp [normalGraphLowerCoefficientMapOver,normalGraphLowerCoefficients,
      Matrix.cons_val_zero,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
    all_goals try simp only [Algebra.smul_def]
    all_goals fun_prop
  exact (hprincipal.prodMk hlower).contDiffWithinAt

end Smoothness
end Lemniscate
