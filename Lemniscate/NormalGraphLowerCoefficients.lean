import Lemniscate.NormalGraphLowerPolynomial
import Lemniscate.NormalGraphRationalSmoothness
import Lemniscate.NormalGraphRationalIdentities

/-! The six lower-order coefficients as smooth maps of the first two height
coordinates in the circle coefficient Banach algebra. Their exact polynomial
identity is lifted from the scalar identity using units of whole coefficient
functions whenever an inverse is evaluated.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

private def normalGraphLowerSample (u : Fin 2 → C(AddCircle T, ℂ))
    (v w : C(AddCircle T, ℂ)) : Fin 4 → C(AddCircle T, ℂ) :=
  ![u 0,u 1,v,w]

private theorem normal_graph_lower_sample_contDiff (v w : C(AddCircle T, ℂ)) :
    ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun u : Fin 2 → C(AddCircle T, ℂ) => normalGraphLowerSample T u v w) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [normalGraphLowerSample] <;> fun_prop

/-- The unit domain depends only on the height and its first derivative. -/
def normalGraphLowerCoefficientDomain
    (K : BackgroundJetOver C(AddCircle T, ℂ)) :
    Set (Fin 2 → C(AddCircle T, ℂ)) :=
  (fun u => normalGraphLowerSample T u 0 0) ⁻¹' normalGraphCoefficientDomain T K

/-- The existing six coefficients, bundled as a map on two height coordinates. -/
def normalGraphLowerCoefficientMap
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (u : Fin 2 → C(AddCircle T, ℂ)) : Fin 6 → C(AddCircle T, ℂ) :=
  normalGraphLowerCoefficients K c (u 0) (u 1)

set_option maxHeartbeats 800000 in
theorem normal_graph_lower_coefficients_smooth
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) :
    IsOpen (normalGraphLowerCoefficientDomain T K) ∧
      (0 : Fin 2 → C(AddCircle T, ℂ)) ∈ normalGraphLowerCoefficientDomain T K ∧
      ∀ u ∈ normalGraphLowerCoefficientDomain T K,
        ContDiffAt ℂ (⊤ : WithTop ℕ∞) (normalGraphLowerCoefficientMap T K c) u := by
  obtain ⟨hopen,hzero,hsmooth⟩ := normal_graph_coefficients_smooth T K c
  have hopen' : IsOpen (normalGraphLowerCoefficientDomain T K) :=
    hopen.preimage (normal_graph_lower_sample_contDiff T 0 0).continuous
  have hzero' : (0 : Fin 2 → C(AddCircle T, ℂ)) ∈
      normalGraphLowerCoefficientDomain T K := by
    change normalGraphLowerSample T 0 0 0 ∈ normalGraphCoefficientDomain T K
    have hs : normalGraphLowerSample T (0 : Fin 2 → C(AddCircle T, ℂ)) 0 0 =
        (0 : Fin 4 → C(AddCircle T, ℂ)) := by
      funext i
      fin_cases i <;> rfl
    rw [hs]
    exact hzero
  refine ⟨hopen',hzero',?_⟩
  intro u hu
  have hsample (v w : C(AddCircle T, ℂ)) :
      normalGraphLowerSample T u v w ∈ normalGraphCoefficientDomain T K := by
    exact hu
  have hb (v w : C(AddCircle T, ℂ)) :
      ContDiffAt ℂ (⊤ : WithTop ℕ∞)
        (fun y : Fin 2 → C(AddCircle T, ℂ) =>
          normalGraphRationalFlow K c ⟨y 0,y 1,v,w,0⟩) u := by
    have h := ((hsmooth _ (hsample v w)).snd).comp u
      (normal_graph_lower_sample_contDiff T v w).contDiffAt
    simpa only [Function.comp_def,normalGraphLowerOrderCoefficient,
      normalGraphLowerSample,Matrix.cons_val_zero,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons] using h
  have hb₀₀ := hb 0 0
  have hb₁₀ := hb 1 0
  have hbm₀ := hb (-1) 0
  have hb₂₀ := hb 2 0
  have hb₀₁ := hb 0 1
  have hb₁₁ := hb 1 1
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp [normalGraphLowerCoefficientMap,
    normalGraphLowerCoefficients,Matrix.cons_val_zero,Matrix.cons_val,
    Matrix.head_cons,Matrix.tail_cons] <;> fun_prop

/-- Evaluation of these coefficients uses the unit hypotheses for the whole
functions A and H in each sample of the original rational flow. -/
theorem normal_graph_lower_coefficients_apply
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (u : Fin 2 → C(AddCircle T, ℂ))
    (hu : u ∈ normalGraphLowerCoefficientDomain T K) (x : AddCircle T)
    (i : Fin 6) :
    normalGraphLowerCoefficientMap T K c u i x =
      normalGraphLowerCoefficients
        ⟨K.k x,K.ks x,K.kss x,K.ksss x,K.eta x,K.b x⟩ c (u 0 x) (u 1 x) i := by
  have hA (v w : C(AddCircle T, ℂ)) :
      IsUnit (graphA K ⟨u 0,u 1,v,w,0⟩) := hu.1
  have hH (v w : C(AddCircle T, ℂ)) :
      IsUnit (graphMetricSquared K ⟨u 0,u 1,v,w,0⟩) := hu.2
  have heval (v w : C(AddCircle T, ℂ)) :
      normalGraphRationalFlow K c ⟨u 0,u 1,v,w,0⟩ x =
        normalGraphRationalFlow
          ⟨K.k x,K.ks x,K.kss x,K.ksss x,K.eta x,K.b x⟩ c
          ⟨u 0 x,u 1 x,v x,w x,0⟩ := by
    simpa only [ContinuousMap.zero_apply] using
      normal_graph_rational_flow_apply T K c ⟨u 0,u 1,v,w,0⟩ (hA v w) (hH v w) x
  have htwo : (2 : C(AddCircle T, ℂ)) x = (2 : ℂ) := rfl
  fin_cases i <;> simp [normalGraphLowerCoefficientMap,
    normalGraphLowerCoefficients,Matrix.cons_val_zero,Matrix.cons_val,
    Matrix.head_cons,Matrix.tail_cons,ContinuousMap.sub_apply,
    ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,
    heval,htwo,ContinuousMap.zero_apply,ContinuousMap.one_apply,
    ContinuousMap.natCast_apply,ContinuousMap.neg_apply]

/-- The complete lower-order coefficient is exactly a polynomial in the
second and third height coordinates with these six smooth coefficients. -/
theorem normal_graph_lower_order_coefficient_polynomial
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (z : Fin 4 → C(AddCircle T, ℂ))
    (hz : z ∈ normalGraphCoefficientDomain T K) :
    let B := normalGraphLowerCoefficientMap T K c ![z 0,z 1]
    normalGraphLowerOrderCoefficient T K c z =
      B 0+B 1*z 2+B 2*(z 2)^2+B 3*(z 2)^3+B 4*z 3+B 5*z 2*z 3 := by
  have hu : ![z 0,z 1] ∈ normalGraphLowerCoefficientDomain T K := by exact hz
  apply ContinuousMap.ext
  intro x
  change normalGraphRationalFlow K c ⟨z 0,z 1,z 2,z 3,0⟩ x = _
  rw [normal_graph_rational_flow_apply T K c _ hz.1 hz.2 x]
  simp only [ContinuousMap.add_apply,ContinuousMap.mul_apply,
    ContinuousMap.pow_apply,ContinuousMap.zero_apply,
    normal_graph_lower_coefficients_apply T K c _ hu x,
    Matrix.cons_val_zero,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  exact normal_graph_lower_polynomial
    ⟨K.k x,K.ks x,K.kss x,K.ksss x,K.eta x,K.b x⟩ c
    (z 0 x) (z 1 x) (z 2 x) (z 3 x)

end Lemniscate
