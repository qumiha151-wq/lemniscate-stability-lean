import Lemniscate.PeriodicBlochSpectrumBound
import Lemniscate.PeriodicRotationSineMass
import Lemniscate.PhysicalTime

/-!
Current manuscript SHA-256: 7e13033f5c3d3f0022b6172007ad1aeb54b810b682a5cfacd6880f6a9b4aff98

The uniform Bloch bound Re z <= -alpha^2/2 for |alpha| <= 1/2 is proved
for the actual circle differential operators, under the explicit profile
and Fourier hypotheses in the manuscript. Compact resolvent, closedness
on the weak H4 domain, and Fourier parity splitting are included. The
single-period nonzero spectral bound -21/4 is also proved.

This remains a partial formalization. The full stability theorem has not
been proved in Lean. Concrete Jacobi-profile identification, the finite
Bloch decomposition on multiple covers, the analytic phase-diffusion
branch, parabolic stability, and geometric convergence remain unproved.

Checked environment: Lean 4.33.1 and Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.
Only compiled Lean source is published. Conditional intermediate results
must not be interpreted as a proof of the full nonlinear theorem.
-/
