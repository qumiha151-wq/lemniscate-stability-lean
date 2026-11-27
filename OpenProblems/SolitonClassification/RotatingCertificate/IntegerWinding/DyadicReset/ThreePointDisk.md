# A square inside the physical shooting arc

In similarity-center coordinates, the convex hull of an actual unit-speed arc contains the square $[-1/20,1/20]^2$. This holds separately for **every** initial parameter in the published closing cube. It only needs 640 positive and 3,200 negative polynomial cells. The full loop uses 4,000 on each side.

For a state with normal support $p$, tangential support $q$, and tangent angle $\theta$, its physical position is $(q\cos\theta-p\sin\theta,q\sin\theta+p\cos\theta)$. The interval argument transports the original differential equation through both finite prefixes and identifies its solution with a single initial-value trajectory. Lean checks the derivative of the position with respect to arclength and obtains the unit tangent $(\cos\theta,\sin\theta)$ throughout the intervening arc. [Physical equation and tangent](../../../SolitonClassification/Rotating/ResetHullArcKinematics.lean)

The three points are enclosed as follows. Each finite decimal denotes an exact rational.

| Sample | Horizontal coordinate | Vertical coordinate |
| --- | --- | --- |
| Initial point | $[-0.13,-0.08]$ | $[0.13,0.19]$ |
| Positive arm, node 636 | $[2.0,2.2]$ | $[0.60,0.73]$ |
| Negative arm, node 3193 | $[-2.7,-2.5]$ | $[-2.1,-1.9]$ |

For any point in the stated square, all three oriented subtriangle areas have the same strict sign. Dividing the areas by their sum expresses the point as a convex combination of the three sampled positions. The intervals are obtained from exact signed dyadic data and uniform nonlinear transport on the parameter cube, with exact rational enclosures for trigonometric errors. [Exact coordinate boxes and square](../../../SolitonClassification/Rotating/ResetHullSamples.lean) · [Oriented-area proof](../../../SolitonClassification/Rotating/ResetThreePointHull.lean)

For the closed profile, the reconstruction identifies the actual arclength coordinates on the common segment. The indexed closing theorem preserves the square, the signed turn of minus one, the shortest period, the sign change of curvature, and the nonzero rotation contribution. Once the two full sets of polynomial cell tests have been checked, the convex hull of every time slice obtained by rotating and dilating this profile about the same fixed center contains that center. The square already proved for the arc is independent of that final closing step. [Closing implication](../../../SolitonClassification/Rotating/IntegerHullIndexed.lean)
