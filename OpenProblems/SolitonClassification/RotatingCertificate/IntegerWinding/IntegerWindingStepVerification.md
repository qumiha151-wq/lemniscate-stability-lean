# Validated Taylor steps for the winding-one rotating shooting problem

The state has coordinates \((k,k'/8,p,q,b,\theta)\) and follows the six-dimensional polynomial field used in the [winding-one construction](IntegerRotatingWinding.md). The five input parameters vary independently in the closed cube of radius \(10^{-30}\) about the [published centre](center.json). The half-period parameter is \(l\), so each input has its own signed first step \(\pm l/4000\).

Lean proves that both first endpoints of this entire cube lie in six explicit rational intervals. The largest radius, including the analytic truncation allowance, is less than \(1.097\times 10^{-30}\). The following centres are rounded for display. The two source tables give the exact integers on the mesh \(10^{-64}\). [Endpoint theorem](../../SolitonClassification/Rotating/IntegerWindingFirstBox.lean) · [Endpoint tables](../../SolitonClassification/Rotating/IntegerWindingFirstReplay.lean)

| Step | \(k\) | \(k'/8\) | \(p\) | \(q\) | \(b\) | \(\theta\) |
|---|---:|---:|---:|---:|---:|---:|
| Positive | 7.752405804 | −0.221247746 | 0.163535941 | −0.088660826 | 0.106444255 | 0.058584967 |
| Negative | 7.752501709 | 0.219658178 | 0.151166045 | −0.122241422 | 0.106444255 | −0.058585329 |

The negative endpoint has positive curvature derivative. At the marked initial point that derivative equals the positive shooting amplitude times the negative first phase coefficient. Consequently each trial has an interior curvature maximum between physical arclengths `−l/4000` and zero, by continuity and the signs at the endpoints. This conclusion already holds before a shooting root is selected.

The same analytic theorem applies to every initial point in the larger box

\[
 |k|\le8.3,\quad |k'/8|\le4.3,\quad |p|,|q|\le7.2,\quad |b|\le0.12
\]

and allows any real initial angle. For each time sign, Picard–Lindelöf gives a trajectory of the original polynomial equation through the point. Throughout \(0\le t\le1561/200000\), its distance in the maximum norm from the canonical degree-60 Taylor polynomial is at most \(2\times10^{-59}\). Uniqueness extends the estimate to any supplied trajectory through the same initial point. The finite recursion yields a velocity defect of at most \(10^{-57}\). The coefficient table and both interval Horner evaluations are checked by the Lean kernel. [Residual bound](../../SolitonClassification/Rotating/IntegerWindingLocalMajorant.lean) · [True-solution estimate](../../SolitonClassification/Rotating/IntegerWindingTrueStep.lean) · [Uniqueness](../../SolitonClassification/Rotating/IntegerWindingStepUniqueness.lean) · [Coefficient checks](../../SolitonClassification/Rotating/IntegerWindingFirstTable.lean)

There is also a general minimum-period check for the four active support variables at fixed pitch. A nonconstant periodic trajectory in the certificate's outer box has \(18P\ge4\) for each positive period \(P\). Given an actual closed trajectory and the requisite mesh enclosures and prime-index separation witnesses, the verified criterion distinguishes its least period from a multiple. [Period theorem and prime checks](../../SolitonClassification/Rotating/IntegerOrbitPeriod.lean)

The archived Arb reports give maxima inside the larger box on both signed grids. The full 8,000 resets, their propagated state and variational errors, the nonlinear shooting zero, the geometric winding and the local classification use the interval-arithmetic and written proof. The exact first endpoints and the analytic estimates above have independent Lean proofs. From the independent classification project root, run `lake build SolitonClassification.AxiomAudit` with the project toolchain. [Audit record](IntegerWindingStepVerification.json)
