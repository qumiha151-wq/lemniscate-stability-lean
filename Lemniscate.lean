import Lemniscate.PeriodicBlochCenterPolynomial
import Lemniscate.PeriodicFiniteNormalization
import Lemniscate.PeriodicOperatorClosed
import Lemniscate.PeriodicRotationSineMass
import Lemniscate.PhysicalTime

/-!
Current manuscript SHA-256: ba2ac80cbb0b78f19d3ac87068d46e445637d74b0dcf7933d9ce2a000b4bfe81

These imports expose the current partial proof and their transitive dependencies.
They do not constitute a Lean proof of the manuscript's main stability theorem.
In particular, the concrete Jacobi data, even Bloch bound, multiple-cover
decomposition, parabolic stability and geometric convergence remain unproved.
Conditional operator theorems retain their explicit profile hypotheses.

RotationKernel was superseded for this paper by circle_rotation_h4_kernel in
PeriodicRotationDomain. The unused alternative matrix-certificate argument is
kept outside the current proof until connected to the actual operator.
-/
