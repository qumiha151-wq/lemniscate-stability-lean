import LengthGrowth.ActualFlow.ArclengthCoercivity
import LengthGrowth.ActualFlow.NormalizedProduct
import LengthGrowth.ActualFlow.ForwardDissipation
import LengthGrowth.SubsqrtGrowth
import LengthGrowth.CurveFromPosition
import LengthGrowth.ScalarDissipation
import LengthGrowth.ElasticStress
import LengthGrowth.AbsoluteCurvatureCoercivity
import LengthGrowth.CircleConnectionBacktracking

/-!
Length-growth question: STATIC GEOMETRIC COERCIVITY AND PARTIAL DYNAMICS.

`FreeElasticScalar.secant_sq_le_energy_drop` derives a finite-interval
secant bound from scalar derivative and dissipation hypotheses. The new
ActualFlow chain derives those laws from a genuine smooth periodic position
family satisfying the actual normal FEF equation on an open time domain:
L' = integral k F ds and E' = -integral F^2 ds. Actual spatial-jet continuity
extends the integral and secant laws to initial time. For a global forward
classical normal FEF with the stated initial regularity it proves
L(t)/sqrt(t) tends to zero. It proves neither global existence for arbitrary
initial curves nor the unrestricted quarter-power upper bound.

`FreeElasticScalar.conditional_fourth_power_bound` uses the intermediate
value theorem and assumes the restart estimate and a uniform bound on
E(s)*L(s). It proves L(t)^4 <= max ((2*L(0))^4) (16*K^2*t), without
assuming monotonicity of length. The uniform normalized-energy bound
remains a hypothesis, not a proved property of every geometric flow.

Run this independent project from its own directory:
  lake +leanprover/lean4:v4.33.1 update
  lake +leanprover/lean4:v4.33.1 exe cache get
  lake +leanprover/lean4:v4.33.1 build

This project does not import the stability or migration projects.

The static geometric proof now derives, for every `ClosedFrenetCurve`,
  2^(-24) * |k(s)|^6 <= E*D,
  2^(-18) * E^5/A^6 <= D,
where E, D and A are the actual integrals of k^2/2, (k''+k^3/2)^2 and |k|.
Closure, the positive curvature maximum, stress estimates and the closing
contradiction are derived from the periodic curve and Frenet equations.
The final theorems assume no coercivity or stress bound.
A uniform bound on total absolute curvature along arbitrary flows is still
missing. These static estimates do not resolve general quarter-power growth.

`CircleConnection.SupportProfile.not_monotone_curvature` rules out globally
nondecreasing curvature in a profile joining the two oriented unit-circle
states. It uses only the Frenet support equations and endpoint limits.
It does not assert existence of such a profile or a general growth bound.
-/

/-!
The actual arclength adapter constructs a global smooth parameter inverse
from arbitrary-speed position and transports curvature, force, E, D and A.
It supplies the legacy static coercivity bounds for the actual material
integrals of each forward slice, including time zero. It also proves E>0
and the coarse bound A>=1; it does not prove a uniform-in-time A bound.

For actual forward normal FEF, NormalizedProduct defines e=E L and proves
e'=E ell-L D, (e^2)'<=E^4, and
e(t)^2-e(s)^2<=integral_s^t E(r)^4 dr for 0<=s<=t.
No energy-clock or ancient-limit theorem is included. The unrestricted
fourth-root growth question remains open. See ArclengthAndProductScope.txt.
-/
