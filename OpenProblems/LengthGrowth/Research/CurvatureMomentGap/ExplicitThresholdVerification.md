# An explicit threshold for the cubic curvature moment

For a periodic closed planar free elastic flow, let \(L\) be length, \(E=\frac12\int k^2\,ds\) bending energy, and \(G=\sqrt L\,|\int k^3\,ds|/(2E)^{3/2}\). The Lean project proves the following results for one explicit \(g_*\in(0,1/2)\).

- If \(G(t)>g_*\) for all sufficiently large \(t\), then \(L(t)=O((1+t)^{1/4})\) and \(E(t)=O((1+t)^{-1/4})\). The same holds when \(\liminf_{t\to\infty}G(t)>g_*\).
- Initial turning number zero implies \(\liminf_{t\to\infty}G(t)\le g_*\). This conclusion covers all smooth forward normal free elastic flows with zero signed total curvature.

The final Lean declarations are `quarter_bounds_of_eventual`, `quarter_bounds_of_liminf`, and `zero_turn_liminf` in `LengthGrowth.ActualFlow.ExplicitCubicThreshold`. The same module proves the static estimate for every periodic regular material position, constructs the window comparison and proves the range of the explicit threshold. The general quarter-power growth question remains open for flows outside the hypotheses above. [Final Lean theorems](../../LengthGrowth/ActualFlow/ExplicitCubicThreshold.lean)

## Constants

The explicit constants in the finite-window argument are
\[
 m=\frac1{1000\cdot161^3},\quad M=\frac{512}{m^2},\quad A=20M,\quad
 T=\frac{256\pi A}{m},\quad K=2(A+1)^2+2,\quad
 \tau=\frac m{16}e^{-KT},
\]
\[
 \epsilon=\min\{1/8,m/16,m^2\tau^2/(1024T^2)\},\qquad g_*=\tfrac12-\epsilon .
\]
The result uses exact real constants throughout. [Lean constants and comparison](../../LengthGrowth/ExplicitWindow.lean) · [Finite-window proof](FiniteWindowThreshold.md)

## Proof dependencies

1. On a unit interval, the curvature and residual have enough integral control to bound the initial data and conserved energy of a matching oscillator. A differential comparison controls the distance between its solution and the curvature on a window of length \(T\). [Local estimates](UnitIntervalData.md) · [ODE stability](../../LengthGrowth/OscillatorStability.lean)
2. The scalar oscillator \(z''=-z^3/2+z/4+1/4\) has a global solution for every pair of initial data. An angular time parametrisation and quartic quadrature give the period and a positive lower bound for its window average. [Existence](../../LengthGrowth/OscillatorExistence.lean) · [Window mean](../../LengthGrowth/OscillatorMeanFloor.lean)
3. Integrating translated finite windows gives the scalar cubic gap. The kernel checks periodic Fubini, variance, the measure of the bad origins, orientation reversal and the exact mean-square residual identity. [Scalar integral argument](PeriodicWindowGap.md)
4. Rescaling arclength by the curvature RMS identifies the scalar quantities with the actual material integrals. The existing flow transfer then gives the rate bounds and the conclusion for turning number zero. [RMS normalization](RMSNormalization.md) · [Material slice adapter](../../LengthGrowth/ActualFlow/CriticalRMSWindow.lean)

The verification record gives the baseline Git revision, source and object hashes of the recompiled modules, project root and namespace-wide audit. The original audit enumerates declarations in the `LengthGrowth` and `FreeElasticScalar` namespaces and rejects axioms outside `propext`, `Classical.choice` and `Quot.sound`. [Verification record](ExplicitThresholdVerification.json)
