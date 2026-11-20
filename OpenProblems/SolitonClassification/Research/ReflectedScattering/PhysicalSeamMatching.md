# Matching at a fixed physical radius

On a physical shot write \(p=X\cdot N,\ q=X\cdot T\) and \(\lambda=|X|^{1/3}\). The normalized curvature and its first derivative use units \(\lambda,\lambda^2\). Let \(R\) be the square root of the normalized stress amplitude, \(U,w\) the oscillator coordinates, and \(a,b\) the radial and transverse components of the stress direction. Thus \(a^2+b^2=1,\ U^4/4+w^2=1\). The incoming branch is \(a\ge0\). The raw impact is \(I=Rb\).

## Why equality of the section data recovers a physical trajectory

Put \(h=Ra\). Then \(R=\sqrt{h^2+I^2}\). At fixed \(U,w,I\), the corrected incoming height becomes the single real function
\[
F(h)=Rh+\frac{Uw(h^2-I^2)+U^3hI}{3R^3}.
\]
For \(R\ge4\) its derivative exceeds or equals one. Indeed write \(Q=Uw(h^2-I^2)+U^3hI\). Using \(|U|\le2,\ |w|\le1,\ |h|,|I|\le R\) gives \(|Q|\le10R^2,\ |Q'|\le12R\). Consequently
\[
F'(h)=R+\frac{h^2}{R}+\frac{Q'}{3R^3}-\frac{Qh}{R^5}\ \ge\ R-\frac{14}{R^2}\ \ge\ 1 .
\]
Along \(h\ge0\), the radius is nondecreasing in \(h\), so the entire interval between two candidate heights remains in \(R\ge4\). Thus at a given corrected height the two oscillator coordinates and \(I\) determine \(h,R,a,b\) uniquely. The estimate also works for large impact.

Writing \(u=U^2/2\), the remaining data are recovered from
\[
k=\lambda R U,\qquad k_s=\lambda^2 R^2 w,\qquad
p=\lambda^3(wa+ub),\qquad q=\lambda^3(ua-wb).
\]
Hence equality of the physical radius and the three section data gives equality of the *full* physical support state. If a shot from the centre reaches that state at arclength \(s>0\) and the shot from a seam reaches it at \(t<0\), the first shot reaches the seam at \(s-t>0\) by uniqueness. The two reflections then give a smooth periodic unit-speed immersion of period \(4(s-t)\), signed turning number zero, and initial curvature derivative equal to the centre marker. [Section coordinates](../../SolitonClassification/IncomingSectionCoordinates.lean) · [Physical coordinate recovery](../../SolitonClassification/PhysicalSectionInjective.lean) · [Closing the physical curve](../../SolitonClassification/ExactPhysicalMatching.lean)

## The actual seam side of the crossing

Start the global normalized support equation at \((c,0,1,0)\), with \(-1/4\le c\le1\) and small constant drive \(d\). At \(d=0\) the entire compact family escapes past every fixed large radial stress level and eventually crosses each large corrected level transversely. On a compact time interval containing all its crossings, the true corrected-height derivative remains positive for all sufficiently small \(d\). This supplies a unique crossing in that interval, whose time is jointly continuous and uniformly Lipschitz in \(d\). The physical radius can therefore be prescribed by the scalar inversion proved in this project.

For every sufficiently large corrected height \(H\), the resulting seam family has a common positive interval of inverse-radius parameters extending continuously to the frozen boundary. The left and right endpoints of the curvature interval retain strictly negative and strictly positive raw impact, respectively. The normalized oscillator point has a single bounded continuous real angle on the whole parameter rectangle. These statements preserve the physical scale when matching to an incoming centre shot. [Choosing the physical radius](PrescribingThePhysicalRadius.md) · [Actual seam crossings](../../SolitonClassification/PrescribedSeamSections.lean) · [Physical realization](../../SolitonClassification/PrescribedPhysicalChart.lean)

## The actual centre side

With centre curvature derivative \(b>0\), set \(\delta=1/b\) and \(\tau=s/\sqrt b\). There are constants \(L_0,C\) independent of \(b\) such that, for \(L\ge L_0\) and \(b\ge32L\), the actual centre shot reaches \(r^3=L/b\) at some \(1\le\tau\le10000\), where \(r\) is the square root of the outer stress amplitude. The radial position component along the stress direction exceeds \(1/1200\); the transverse component \(\zeta\) satisfies \(L|\zeta|^3\le C^3/L^2\); and the accumulated angle is at least \(b/8\). The proof starts at the actual centre data and uses a first-exit argument. [Descent proof](CentreToCriticalLayer.md) · [Centre trajectory and critical level](../../SolitonClassification/CentreCriticalLayer.lean)

Choose a fixed sufficiently large incoming height \(H\). All sufficiently large centre shots begin the controlled portion of their trajectory above that height and leave it below. Every crossing has strictly negative height derivative in the time direction of the shot. Each shot therefore has a unique first crossing on the controlled interval. Joint continuity of the height near this interval and compactness of the segment before the crossing make its time continuous in the initial slope. At the crossing the impact has absolute value at most \(K/H\), the inverse radius tends to zero as the initial slope grows, and the continuous angle lift is at least \(b/8\). [Centre estimates](PhysicalIncomingCrossing.md) · [Continuous choice of first crossing](../../SolitonClassification/PhysicalCentreSelector.lean) · [Angle as a function of the marker](../../SolitonClassification/CentrePhaseContinuity.lean)

## Closure for arbitrarily large markers

Choose \(H\) so that \(K/H\le 0.001\). The impact difference has opposite signs on the two seam-curvature edges of a shooting rectangle. The seam angle stays bounded on its parameter rectangle, while the centre angle crosses arbitrarily large multiples of \(2\pi\). For any lower bound on the initial slope we can therefore choose two marker edges and an integer phase level with opposite angle differences on those edges. The two-dimensional intermediate value theorem gives a simultaneous zero. Both shots use the same physical radius at that zero. The coordinate recovery above then closes an actual geometric expander with centre curvature derivative larger than the chosen bound. Its total signed curvature over the constructed period is zero. [Rectangle matching](../../SolitonClassification/MatchCertifiedSeam.lean) · [Unconditional theorem](../../SolitonClassification/UnboundedClosedExpanders.lean)

A further Lean theorem constructs a sequence of pairwise geometrically inequivalent closed profiles. For a single smooth periodic curve, the maximum of the absolute curvature derivative is finite. The unit-speed condition forces the derivative of a change of parameter between similar unit-speed profiles to be constant. The normalized expander equation then forces the spatial scale to equal one and the dilation centres to agree. The maximum absolute curvature derivative is consequently unchanged by such a similarity or a repeated traversal. Recursively choose the next centre slope above the preceding maximum. The resulting sequence has strictly increasing maxima. [Geometric equivalence](../../SolitonClassification/GeometricSimilarity.lean) · [Infinite family of inequivalent profiles](../../SolitonClassification/InfinitelyManyExpanders.lean)

For the quantitative count, keep the left marker edge fixed and put the right edge at \(B_0+C(N+1)\). The lower bound on its angle supplies \(N\) well-separated integer multiples of \(2\pi\) between the two edges. The same marker cannot match at two of these levels because the seam angle stays in a bounded interval. Reflection and uniqueness of the support equation make the absolute centre derivative independent of which zero-curvature centre visit is used. Different positive markers thus distinguish geometric similarity classes. This proves a lower bound of \(\lfloor cB\rfloor\) classes with marker at most \(B\) for all sufficiently large \(B\). [Finite matches on one section](../../SolitonClassification/PhysicalMarkerCounts.lean) · [Sharp identification of the marker](../../SolitonClassification/StrongCentreMarker.lean) · [Geometric count](../../SolitonClassification/LinearExpanderCount.lean)
