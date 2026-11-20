# Fixed disks in convex hulls of near-round flows

The physical slab theorem concerns the independent **Migration** project.
The time-dependent curve determines the metric, signed curvature,
elastic force, energy and arclength centroid throughout.

| Lean module | Geometric statement |
| --- | --- |
| `Migration.NearRoundCentroid` | Periodic stress has zero integrated force. The arclength centroid has the centered force rate, and an inverse-energy rate bound can be integrated on a physical time slab. |
| `Migration.NearRoundSupport` | In arbitrary material coordinates, \(L\int(k-S/L)^2ds\le a^2\) bounds the projected position-normal defect by \(a/S\). It gives a support point wherever the required normal direction is attained. |
| `Migration.NearRoundDrift` | Actual force and the curvature oscillation give \(\lvert B'\cdot e\rvert L\le a(1+(1+a)/S)\sqrt L\sqrt D\) for each unit projection. |
| `Migration.NearRoundVirial` | Projecting the vector-valued centroid gives the scalar material centroid. The signed normal support bounds and the dilation virial identity hold for the position-defined slice. The virial accepts any spatial origin. |
| `Migration.NearRoundDirections` | A global height maximum, periodicity and the defect estimate yield the required normal direction on the original curve. |
| `Migration.NearRoundEnergy` | The signed curvature integral gives \(2EL=S^2+\mathcal O\). The physical virial and the signed normal support give \(E\le (1+a) L^{3/2}\sqrt D/S\). |
| `Migration.NearRoundCore` | Every unit direction has an actual curve point with height at least \(e\cdot B(s)+9L(t)/(16S)\). |
| `Migration.NearRoundConvexDisk` | A strict support margin yields inclusion in the ordinary convex hull. A finite subcover of the direction circle supplies a finite polygon, and Hahn–Banach separation and the real Riesz representation theorem finish the argument. |
| `Migration.NearRoundDisk` | The actual convex hull at time \(t\) contains the closed ball of center \(B(s)\) and radius \(L(t)/(2S)\). The physical ball of center \(B(s)\) and radius \(S/(4E(s))\) is contained in every hull throughout the slab. |

The final hypotheses are a smooth periodic immersed pure normal free
elastic flow on an open time interval containing the chosen closed
slab, its physical signed curvature integral equal to the constant
\(S\ge2\) throughout, and \(\mathcal O\le1/64\) on every slice.
Orienting a physical curve of nonzero turning number positively gives
\(S=2\pi|n|\). The Lean theorem takes the signed integral explicitly.

The single-initial-slice corollary uses the oscillation inequality of
Andrews and Wheeler. That literature estimate and its small-data
argument are justified in the mathematical manuscript. The arbitrary
turning number short-time statement has its separate mathematical proof.
[Near-round manuscript](NearRoundFixedCore.md) and
[short-time manuscript](ShortTimeFixedCore.md)
