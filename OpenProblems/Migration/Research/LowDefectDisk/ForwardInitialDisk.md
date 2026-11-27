# The initial curve at the one-sided time boundary

Consider a classical closed free elastic flow on \(t\ge0\). The normal evolution equation need only be known for \(t>0\). The initial immersion has positive speed, and physical position, speed and curvature extend jointly and continuously to \(t=0\). If \(2E(0)L(0)\le4\pi^2+11/2\), then
\[
\overline B\!\left(c(0),\,\frac{85\pi}{100E(0)}\right)
 \subseteq \bigcap_{t\ge0}\operatorname{conv}X(t).
\]
Here \(E=\tfrac12\int k^2\,ds\) and \(c=L^{-1}\int X\,ds\). The hypothesis allows equality in the initial threshold. [Classical forward theorem](../../Migration/SublevelForwardGeometry.lean)

The initial threshold propagates by a limiting argument. If the normalized bending \(2EL\) first exceeded the prescribed cap at some positive time, one could choose an intermediate threshold between the initial cap and the smaller of the putative excess value and \(4\pi^2+36\). Continuity gives a positive starting time below that intermediate threshold. The strict sublevel propagation for interior times contradicts the putative excess. [Initial threshold and positive-time hulls](../../Migration/SublevelForwardLimit.lean)

To pass a point \(z\) of the fixed initial disk into a later hull at \(t>0\), approach \(0\) from positive times \(v<t\) using
\[
c(v)+\frac{E(0)}{E(v)}(z-c(0)).
\]
This point is in the disk for start time \(v\) and tends to \(z\). The later hull is closed. To include the initial hull itself, joint position continuity and compactness of the material period interval give continuity of the maximum of every fixed linear functional on the moving trace. A point separated from the initial hull would also be separated from sufficiently early positive-time hulls. [Very first hull](../../Migration/SublevelForwardHull.lean)

The endpoint continuity of bending, length, and centroid follows by integrating the continuous position, speed and curvature on the fixed material interval. Bending at time zero is strictly positive by positive-time dissipation and the positive bending of a regular closed curve. The conclusion excludes migration under the initial threshold. The unrestricted existence question remains open.
In the straight-line definition of migration, any separated pair of material traces therefore forces the strict initial lower bound \(2E(0)L(0)>4\pi^2+11/2\). [Necessary condition for migration](../../Migration/SublevelMigrationFloor.lean)
