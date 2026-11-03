import Lemniscate.NormalGraphRationalSmoothness
import Lemniscate.PeriodicCoefficientAlgebra
import Lemniscate.PeriodicSobolevH4Jet

/-! The rational normal-graph equation on the complete periodic H4 space.

The circle variable is x = sqrt(2)*s. Thus the first four continuous height
coordinates are f, sqrt(2)*f_x, 2*f_xx, 2*sqrt(2)*f_xxx, whereas the fourth
physical derivative is the L2 element 4*f_xxxx. This is a rational complex
extension near zero. Its identification with real geometric flow and its
linearized spectral operator are separate proof obligations.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

def circleNormalGraphCoordinates :
    CircleSobolevSpace T 4 →L[ℂ] (Fin 4 → C(AddCircle T, ℂ)) :=
  ContinuousLinearMap.pi fun j =>
    (![1,((Real.sqrt 2:ℝ):ℂ),2,((2*Real.sqrt 2:ℝ):ℂ)] j) •
      ((ContinuousLinearMap.proj j).comp (circleSobolevContinuousJet T))

theorem circle_normal_graph_coordinates (f : CircleSobolevSpace T 4) :
    circleNormalGraphCoordinates T f =
      ![circleSobolevContinuousJet T f 0,
        ((Real.sqrt 2:ℝ):ℂ) • circleSobolevContinuousJet T f 1,
        (2:ℂ) • circleSobolevContinuousJet T f 2,
        ((2*Real.sqrt 2:ℝ):ℂ) • circleSobolevContinuousJet T f 3] := by
  funext j
  fin_cases j <;> simp [circleNormalGraphCoordinates]

def circleNormalGraphDomain (K : BackgroundJetOver C(AddCircle T, ℂ)) :
    Set (CircleSobolevSpace T 4) :=
  (circleNormalGraphCoordinates T) ⁻¹' normalGraphCoefficientDomain T K

def circleNormalGraphFlow (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) (f : CircleSobolevSpace T 4) : CircleL2 T :=
  circleCoefficientMultiplyL2 T
      (normalGraphPrincipalCoefficient T K (circleNormalGraphCoordinates T f))
      ((4:ℂ) • circleSobolevCoordinate T 4 4 f)+
    circleContinuousL2 T
      (normalGraphLowerOrderCoefficient T K c (circleNormalGraphCoordinates T f))

/-- The full H4-to-L2 map is smooth on a common open neighborhood of zero.
This uses the complete Sobolev norm and keeps the fourth derivative in L2. -/
theorem circle_normal_graph_flow_smooth (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) :
    IsOpen (circleNormalGraphDomain T K) ∧
      (0 : CircleSobolevSpace T 4) ∈ circleNormalGraphDomain T K ∧
      ∀ f ∈ circleNormalGraphDomain T K,
        ContDiffAt ℂ (⊤ : WithTop ℕ∞) (circleNormalGraphFlow T K c) f := by
  obtain ⟨hopen,hzero,hcoeff⟩ := normal_graph_coefficients_smooth T K c
  have hdomain : IsOpen (circleNormalGraphDomain T K) :=
    hopen.preimage (circleNormalGraphCoordinates T).continuous
  have hzero' : (0 : CircleSobolevSpace T 4) ∈ circleNormalGraphDomain T K := by
    change circleNormalGraphCoordinates T 0 ∈ normalGraphCoefficientDomain T K
    simpa only [map_zero] using hzero
  refine ⟨hdomain,hzero',?_⟩
  intro f hf
  have hc := (hcoeff (circleNormalGraphCoordinates T f) hf).comp f
    (circleNormalGraphCoordinates T).contDiff.contDiffAt
  have hfourth : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun u : CircleSobolevSpace T 4 => (4:ℂ) • circleSobolevCoordinate T 4 4 u) f :=
    (((4:ℂ) • circleSobolevCoordinate T 4 4).contDiff).contDiffAt
  have hm := (circle_coefficient_multiply_l2_contDiff T).contDiffAt.comp f
    (hc.fst.prodMk hfourth)
  have hb := (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).contDiff.contDiffAt.comp f hc.snd
  exact hm.add hb

end Lemniscate
