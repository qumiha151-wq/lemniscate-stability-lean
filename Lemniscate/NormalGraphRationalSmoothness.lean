import Lemniscate.NormalGraphCoefficientAlgebra
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
  normalGraphCoefficientDomainOver C(AddCircle T, ℂ) K

def normalGraphPrincipalCoefficient (K : BackgroundJetOver C(AddCircle T, ℂ))
    (z : Fin 4 → C(AddCircle T, ℂ)) : C(AddCircle T, ℂ) :=
  normalGraphPrincipalCoefficientOver C(AddCircle T, ℂ) K z

def normalGraphLowerOrderCoefficient (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) (z : Fin 4 → C(AddCircle T, ℂ)) : C(AddCircle T, ℂ) :=
  normalGraphLowerOrderCoefficientOver C(AddCircle T, ℂ) K c z

end Lemniscate
