# Simple inflections in a primitive traversal

Let a smooth closed unit-speed profile of the coefficient-one pure elastic expander equation have a zero-curvature crossing of its dilation centre, with positive curvature derivative \(b\ge 32\). Every positive period of its position contains at least
\[
             \left\lfloor\frac{b}{4608\pi}\right\rfloor
\]
distinct arclength parameters in its interior at which the signed curvature vanishes with nonzero derivative. In particular the lower bound applies to the least period. Together with the unbounded family of centre markers this gives closed profiles of turning number zero with arbitrarily many simple inflections on one primitive traversal. [General inflection bound and existence theorem](../../SolitonClassification/PrimitiveInflections.lean)

Write \(\tau=s/\sqrt b\). The actual Cartesian support coordinates of the geometric curve solve the global shooting equation. The initial displacement estimate gives a component of the rescaled position at least \(1/288\) at \(\tau=1/2\). Consequently the distance from the centre at that time is at least \(\sqrt b/288\). For a positive position period \(d\), reduce this parameter modulo \(d\). Each Cartesian coordinate has derivative of absolute value at most one, so the squared distance is at most \(2d^2\). This gives \(d>\sqrt b/576\). [Radius and period estimates](../../SolitonClassification/CentreExpanderRadius.lean) · [Initial displacement](../../SolitonClassification/CentreShotAlignment.lean)

On \(0\le\tau\le1/576\) the stress stays positive, and the normalized oscillator angle, measured continuously from zero, reaches at least \(b/4608\). Each positive integer multiple of \(\pi\) up to this value occurs by continuity. Its sine vanishes and its cosine is either one or minus one. The physical curvature therefore vanishes with nonzero derivative at the corresponding parameter. Different phase levels give distinct parameters, all strictly before any positive position period. No monotonicity or unique phase hitting time is needed in this last count. [Angle and physical scale](../../SolitonClassification/CentreShotWinding.lean)
