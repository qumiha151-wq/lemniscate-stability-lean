import Lemniscate.LemniscateStability
import Lemniscate.PeriodicCoverUpperBound

/-! Geometric stability of finite Bernoulli lemniscate covers.

The closed theorem `Lemniscate.lemniscate_stability` constructs its
actual arclength coordinate and exact reference length, then proves
the intrinsic curvature-profile stability statement for every positive
covering number. The same limiting rotation and parameter family work
for all spatial convergence orders and quantitative rates.
The constructed flow is jointly smooth in space and time, including
the initial endpoint, on the same initial smallness neighborhood.
The same rotation and reparametrizations give smooth convergence after
division by the evolving curve length. The matching M^(-2) spectral-gap
upper bound records the obstruction to a multiplicity-independent linear
decay exponent.

Current manuscript SHA-256: 2e0877dbc9b6cf4810b8be0229d5fc2e36e3fd96717943a31d895a734482eebf
Checked environment: Lean 4.33.1 and Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.
Only compiled Lean source is published.
-/

#check Lemniscate.lemniscate_stability
