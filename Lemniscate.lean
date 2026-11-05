import Lemniscate.LemniscateStability

/-! Geometric stability of finite Bernoulli lemniscate covers.

The closed theorem `Lemniscate.lemniscate_stability` constructs its
actual arclength coordinate and exact reference length, then proves
the intrinsic curvature-profile stability statement for every positive
covering number. The same limiting rotation and parameter family work
for all spatial convergence orders and quantitative rates.

Current manuscript SHA-256: 175f1ccfba227a6751f9f957e1284dcd67e764459ceeb7cefbe32d6cc1985b42
Checked environment: Lean 4.33.1 and Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474.
Only compiled Lean source is published.
-/

#check Lemniscate.lemniscate_stability
