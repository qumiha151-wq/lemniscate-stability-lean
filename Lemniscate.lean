import Lemniscate.BernoulliParabolicLocalSolution
import Lemniscate.BernoulliParabolicEnergyEstimate
import Lemniscate.PeriodicParabolicLocalSolution
import Lemniscate.PeriodicSobolevEnergyNorm
import Lemniscate.PeriodicParabolicEquation
import Lemniscate.BanachDenseSolvability
import Lemniscate.PeriodicParabolicSolvability
import Lemniscate.PeriodicParabolicUniqueness
import Lemniscate.PeriodicParabolicNormedSpace
import Lemniscate.PeriodicParabolicInverse
import Lemniscate.PeriodicParabolicLowerOrder
import Lemniscate.PeriodicParabolicPicard
import Lemniscate.PeriodicParabolicProducts
import Lemniscate.PeriodicProfileShiftSmoothness
import Lemniscate.PeriodicTimeCoefficientAlgebra
import Lemniscate.NormalGraphModulationConjugation
import Lemniscate.PeriodicParabolicConjugation
import Lemniscate.BernoulliCoverModulationData
import Lemniscate.PeriodicParabolicEnergyIdentity
import Lemniscate.PeriodicParabolicH2EnergyIdentity
import Lemniscate.PeriodicSobolevPrincipalEstimate
import Lemniscate.BernoulliCombinedEnergyEstimate
import Lemniscate.FrenetComparison
import Lemniscate.PeriodicSobolevTranslation
import Lemniscate.NormalGraphRotationGeometry
import Lemniscate.BernoulliCoverModulation
import Lemniscate.PeriodicCoverStableEnergy
import Lemniscate.PeriodicParabolicDataApproximation
import Lemniscate.PeriodicFiniteFourierExtension
import Lemniscate.PeriodicFiniteParabolicEstimates
import Lemniscate.PeriodicTimeNonlinearRemainder
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
geometric curve flow. Conjugation compatibility and uniqueness prove that
the actual local modulated solution is real for real initial heights. Mixed Sobolev product bounds
and a local quadratic Taylor remainder estimate are available.
The nonlinear graph remainder satisfies the mixed H2-H4 two-point bound,
both before and after actual adjoint-normalized rotation modulation on every
positive cover. The lifted adjoint phase functional, its reality and nonzero
pairing with the geometric rotation field are proved. The full covered
operator is dissipative in a bounded L2 metric on that phase kernel, with
rate 21/4 on one period and 1/(2*M^2) on every other positive cover.
Finite Fourier solutions belong to a complete parabolic Banach space with
the true Bochner primitive, H2 initial trace, time-L2 H4 values and physical
velocity. Their maximal-regularity estimate is independent of the mode count.
Actual finite initial and time-forcing data are dense in H2 x time-L2.
The pointwise nonlinear tame bound induces a genuine time-L2 Nemytskii map
and the mixed time estimate; time-continuous H4 values are not assumed.

The infinite-dimensional principal equation is solvable with the same
maximal-L2 estimate and a proved uniqueness theorem. Its actual inverse and
the zero-initial-value estimate give a solution isomorphism for bounded
H2-to-L2 lower-order perturbations on a positive time interval. The nonlinear
contraction theorem uses the genuine time-L2 Nemytskii map. Small H2 initial
heights admit actual local modulated solutions on every positive cover.
The Bochner primitive yields the L2 energy formula without a pointwise time
derivative assumption. Finite Fourier projection and dominated convergence
give the H2 energy formula. Weak integration by parts and interpolation
control the complete H4 norm by the principal elliptic operator. Combining
the principal energy with the cover metric absorbs the actual nonlinear
remainder, for every rate below the proved spectral gap on the phase kernel.
For actual modulated parabolic solutions on each positive cover, a small
continuous-H2 neighborhood preserves the phase and gives exponential energy
decay at every smaller positive rate, together with integrated H4 dissipation.
The combined energy also controls the complete H2 norm.
All integer Sobolev orders admit the actual Haar-preserving spatial
translation, its inverse, coordinate compatibility and strong continuity.
Aligned Frenet curves satisfy direct tangent and position comparison bounds
in terms of their L1 curvature difference, without a Gronwall exponential.

This remains a partial formalization. The full nonlinear stability theorem is
NOT proved. Global continuation, smoothing, curvature-profile entry and
full geometric convergence remain proof obligations.

Checked environment: Lean 4.33.1 and Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.
Only compiled Lean source is published.
-/
