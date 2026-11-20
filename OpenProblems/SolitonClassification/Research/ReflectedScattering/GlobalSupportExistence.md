# Global support trajectories and reflection at the frozen seam

For every real driving rate d and every initial state in ℝ⁴, the polynomial system

    k′ = v,       v′ = −k³/2 − p,       p′ = −kq,       q′ = d + kp

has a unique solution on the whole real arclength axis. The value d = 0 gives the frozen system. The value d = 1 gives the support-coordinate system of a purely dilating profile.

## Global continuation

Multiply the entire field by a common scalar weight μ ∈ [0,1]. Along the resulting trajectories, put

    P = √(1 + p² + q²),       U = √(1 + (k²/2)² + v²).

The curvature terms cancel, giving P′ = μdq/P and U′ = −μpv/U. Hence |P′| ≤ |d| and |U′| ≤ |p|. For |s| ≤ T, put B = P(0) + |d|T. Then P(s) ≤ B and U(s) ≤ U(0) + BT. The four coordinate bounds are

    |p|, |q| ≤ P,       |v| ≤ U,       |k| ≤ 2U + 1.

Consequently R = 2(U(0) + BT) + 1 + B bounds the sup norm on this entire interval, independently of the multiplier.

Choose μ(x) = min(1, max(0, R + 1 − ‖x‖∞)). On the support of this weight, clipping the individual coordinates to [−R−1, R+1] preserves the original field. The clipped polynomial is bounded and Lipschitz by compactness of the coordinate ball and smoothness of the polynomial. Its product with the bounded Lipschitz multiplier is again bounded and Lipschitz. The bounded-field theorem gives a global trajectory for this truncated field. Its a priori bound keeps the trajectory inside the radius R on the desired interval, where the multiplier equals one. For two such intervals, a common cutoff containing both bounds gives agreement on the overlap by uniqueness. Overlapping intervals of arbitrarily large radii therefore give a single differentiable trajectory on ℝ. The same estimate and uniqueness on bounded intervals prove its uniqueness among all global solutions.

## The seam and its two tails

For d = 0, differentiating p² + q² gives zero. Every initial state (c, 0, 1, 0) therefore determines an actual global unit-support frozen orbit. More generally, if any frozen orbit has v(0) = q(0) = 0, the reflected trajectory

    (k(−s), −v(−s), p(−s), −q(−s))

solves the same equation with the same initial state. Uniqueness makes k and p even and v and q odd. The radial stress is odd, the transverse stress and amplitude are even, and the raw impact (root times normalized transverse stress) takes the same value at s and −s.

## Formal interfaces

- ClosedSimilarity.GlobalSupport.exists_unique_solution supplies the unique global trajectory through arbitrary data.
- ClosedSimilarity.GlobalSupport.exists_frozen_seam constructs a FrozenStress.Orbit with the required seam data.
- ClosedSimilarity.FrozenStress.Orbit.seam_reflection and seam_impact_radial_parity give coordinate reflection, raw impact parity and radial stress parity for any frozen orbit with v(0) = q(0) = 0.

The global theorem controls continuation in arclength. Periodicity or closure of a reconstructed profile requires additional information about the selected trajectory.

## Dependence on the initial data and driving rate

Adjoin d as a fifth, constant coordinate. The resulting vector field is again polynomial. For a compact family of initial data and any real T ≥ 0, the explicit bounds above place every extended trajectory on [−T,T] in one compact ball. The polynomial has a common Lipschitz constant K there. Grönwall's inequality, applied forward and to the time-reversed equation, bounds the distance between any two extended trajectories by exp(KT) times the distance between their initial data, uniformly on this interval. Trajectories are continuous in arclength. This estimate gives joint continuity of evaluation in real time, all four initial coordinates, and d, including across the frozen limit d = 0.

The Lean interfaces are ClosedSimilarity.GlobalSupport.compact_initial_estimate and continuous_solution.

## Two explicit tail tests and the moving phase

Suppose a frozen orbit at a finite section S has radial stress below −13 and corrected impact strictly between −0.10 and −0.09. Its raw impact stays below −0.002 for every s ≥ S. If instead its radial stress is below −12 and corrected impact exceeds 0.8, its raw impact stays above 0.52 for every s ≥ S. For seam data, reflection gives the corresponding signs for s ≤ −S. These deductions use explicit differential inequalities for the two stress correctors. Verification of particular numerical endpoint enclosures is a separate computation.

FrozenTailSigns proves the two tail tests. OuterPhase proves the unit-circle formulas for the normalized moving oscillator, including the differentiable phase lift through every curvature zero and extremum. The global existence and continuity results here apply to the full unmodified support polynomial.

## Entrance and matching

Every actual symmetric frozen seam reaches arbitrarily large outgoing radial stress. Beyond a sufficiently late entrance, each sufficiently high corrected stress level has exactly one crossing and its derivative is at least 1/4. A compact continuous family of such seams has a common entrance time for each fixed radial threshold. The full escape argument accompanies this note in FrozenSeamEscape.md.

MarkerCount proves a finite counting assertion for the subsequent rectangle argument. Under its continuity, boundary-sign and phase bounds, separated phase levels force distinct initial markers in a prescribed interval. It does not require that the incoming phase be monotone or that a marker determine a unique seam parameter.
