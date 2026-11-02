import Lemniscate.PeriodicProfileAnalyticEigenpair
import Lemniscate.PeriodicCoverRotation
import Lemniscate.PeriodicRotationSineMass
import Lemniscate.PhysicalTime

/-!
Current manuscript SHA-256: c19d1d216c010870b14f67e89d943110448e107c0e81c2900c1722b1818a51f3

For the actual circle differential operators, the uniform Bloch bound
Re z <= -alpha^2/2 for |alpha| <= 1/2 is proved. The nonzero spectral bounds
are -21/4 on one period and -1/(2*M^2) on M >= 2 covers. The rotational kernel
on a cover is exactly the span of Q*P and has dimension one; there is no
generalized kernel. Profile identities, Fourier coefficients, and periodic
extension data remain explicit hypotheses. Compact resolvent and closedness
on the weak H4 domain are included. An analytic normalized eigenpair
issuing from the rotational mode is constructed using the analytic inverse
function theorem in principal-resolvent coordinates. The cover arguments use Fourier
components directly and assume no spectral decomposition or spectral bound.

This remains a partial formalization. The full stability theorem has not
been proved in Lean. Concrete Jacobi-profile and extension identification,
the real and even phase-diffusion expansion, parabolic stability, and geometric
convergence remain unproved.

Checked environment: Lean 4.33.1 and Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.
Only compiled Lean source is published. Conditional intermediate results
must not be interpreted as a proof of the full nonlinear theorem.
-/
