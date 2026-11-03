import Lemniscate.BernoulliClassicalGraphEquation
import Lemniscate.NormalGraphSobolevConjugation
import Lemniscate.PeriodicSobolevProductDifferences
import Lemniscate.NormalGraphSobolevCoefficientBounds
import Lemniscate.NormalGraphSobolevPolynomial
import Lemniscate.PeriodicRotationSineMass
import Lemniscate.PhysicalTime
import Lemniscate.BernoulliCircleProfile
import Lemniscate.NormalGraphFlowVariation
import Lemniscate.BernoulliArclengthFrame
import Lemniscate.PeriodicSobolevDerivatives
import Lemniscate.LinearParabolicEnergy
import Lemniscate.BernoulliFlowLinearization

/-!
Current manuscript SHA-256: bd1b3239f845fce51d6b9a8c1991be0b7d081b7126897d116189749a1bcebb7e

The actual Bernoulli lemniscate is constructed from its explicit immersion and
scaled-arclength integral coordinate. Its curvature profile, ODE, first integral,
normalization, fundamental period and squared frequency are proved. Its complete
Fourier data follow from an absolutely convergent lattice-row expansion and
elementary geometric sums. No profile or Fourier identity is assumed for this
actual curve.

For every positive cover, the actual weak-H4 differential operator has exactly
the rotational kernel, no generalized kernel, and nonzero spectral gap at least
21/4 on one period and 1/(2*M^2) otherwise. For sufficiently large covers the
gap is also at most K/M^2, with K independent of M. The actual dilation mode
q^3 has eigenvalue -30. The generic conditional spectral lemmas are retained
where they are used to prove these actual-curve conclusions.

The physical-arclength Frenet frame and curvature derivatives are derived from
the actual immersion. The normal-graph speed, signed curvature, support and
elastic force are differentiated geometrically. The actual graph flow has
principal term -g^(-4)*h_ssss, a rational expression with all square roots
cancelled, and the proved pointwise first variation. Real first variation
is obtained by restricting the single complex rational calculation. Its relation to the normalized linearized
expression includes the physical-to-scaled-arclength factors.

Integer-order periodic Sobolev spaces are closed derivative-jet subspaces of a
finite L2 Hilbert product, with their complete derivative square-sum norm. The
H1 continuous representative, bounded order-lowering and weak-differentiation
maps, and the actual classical derivative between the H2 representatives are
proved, using the weak-to-classical derivative bridge.
The graph equation is a smooth map from the complete H4 space into L2 on an
open neighborhood controlled by the H2 norm. At the Bernoulli equilibrium its
Frechet derivative is exactly the differential operator used in the spectral
proof. On classical real graph data this equation agrees with the actual
geometric curve flow. Conjugation compatibility is proved; reality preservation
of evolving solutions still requires uniqueness. Mixed Sobolev product bounds
and a local quadratic Taylor remainder estimate are available.
Finite diagonal parabolic systems satisfy an exact energy identity with a
bound independent of the number of modes.

This remains a partial formalization. The full nonlinear stability theorem is
NOT proved. Infinite-dimensional parabolic solvability, maximal regularity,
nonlinear wellposedness, smoothing, normal stability, curvature-profile entry
and full geometric convergence remain proof obligations. The proved Frechet
linearization and finite-mode energy estimates do not assert these results.

Checked environment: Lean 4.33.1 and Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.
Only compiled Lean source is published.
-/
