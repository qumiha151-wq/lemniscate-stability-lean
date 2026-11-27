# Closed similarity profiles with a countable exceptional set

Let $k(s)$ denote the signed curvature in real arclength of a smooth closed immersed free-elastic similarity profile. Suppose that a single meromorphic function on the complement of a closed countable set $S$ in the complex plane agrees analytically with $k$ along the real axis, and that $S$ does not meet that axis. The set may be unbounded and may have accumulation points. Ordinary poles are allowed outside $S$.

**Every such profile is a covered circle or a covered Bernoulli lemniscate.** On the lemniscate branch the rotation coefficient vanishes. Both classes admit global meromorphic curvature. The proved rotating solution with exactly two transverse double points admits no such continuation for any choice of $S$. [Classification of the actual positions](../../SolitonClassification/CountableCurvatureClassification.lean) · [Rotating example](../../SolitonClassification/EllipticRotatingObstruction.lean)

## Filling the exceptional set

Normalize values at the ordinary poles. An admissible local filling is a meromorphic function on a neighborhood which agrees with the given continuation off $S$. The complement of a countable set provides agreement points arbitrarily near every point of a disk. The meromorphic identity theorem identifies any two fillings as germs. They define one normalized meromorphic function $H$ on the open union $U$ of the neighborhoods admitting a filling. Its closed complement $B$ is a subset of $S$. [Construction and uniqueness](../../SolitonClassification/MeromorphicMaximalDomain.lean)

The real similarity equation gives the fourth-order differential equation for curvature at each real arclength. Its residual is meromorphic on $U$. A countable set cannot disconnect the complex plane, so the identity theorem makes the residual zero on punctured neighborhoods throughout $U$. [Propagation of the physical equation](../../SolitonClassification/CountableTraceEquation.lean)

If $B$ were nonempty, it would have an isolated point $x$. Indeed, a nonempty perfect subset of the plane contains an injective image of Cantor space and is uncountable. On a punctured disk about $x$, $H$ has normalized meromorphic germs and satisfies the ordinary equation. Apply the isolated finite-cover theorem with covering power one. It fills $x$ even if ordinary poles were initially allowed to accumulate there. Normalizing this germ produces an admissible filling, contradicting $x\notin U$. Thus $U$ is the whole plane. The earlier global-meromorphic classification identifies the curve. [Isolated puncture](../../SolitonClassification/CountableSingularityFilling.lean) · [Removal of the closed countable set](../../SolitonClassification/MeromorphicBoundaryRemoval.lean) · [Global geometry](../MeromorphicCurvature/MeromorphicArclength.md)

All steps through the conclusion on the real plane curve are verified in Lean. The existence of a single-valued meromorphic continuation outside some closed countable set is a hypothesis on the complex curvature. An arbitrary smooth closed similarity profile need not satisfy it, as the rotating example shows.

