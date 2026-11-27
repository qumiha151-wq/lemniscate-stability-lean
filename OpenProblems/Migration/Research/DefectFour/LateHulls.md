# Eventual enclosure by the expanding hull under defect thirty-six

For any smooth closed planar free elastic flow with \(L(0)\int k(0)^2\,ds\le4\pi^2+36\), every fixed compact subset \(K\) of the physical plane is eventually contained in the convex hull of the curve, at every sufficiently late time. The assertion allows an arbitrary initial location of \(K\), including a compact set far from the initial curve.

Write \(U=L\int k^2\,ds,\ d=U-4\pi^2,\ R_E=2\pi/\int k^2\,ds\). The [quantitative decay argument](../../../LengthGrowth/Research/BendingSublevel/QuantitativeCircularization.md) gives \(d(t)\to0\). Choose \(T\) with \(d(T)\le4\). The [earlier-centroid disk estimate](FixedDisk.md) applied to the restarted flow gives, for every \(t\ge T\),
\[
 \overline B\big(c(T),\tfrac45R_E(T)+R_E(t)/200\big)\subseteq\operatorname{conv}X(t).
\]

In fact \(R_E(t)\to\infty\) follows directly from the sublevel and the sharp dilation virial. If \(B(t)=\int k^2\,ds\downarrow b>0\), then \(L(t)\le U(0)/b\) and \(D(t)\ge\pi^2 B(t)^2/L(t)^3\) is bounded below by a positive constant. This contradicts energy dissipation \(B'=-2D\). The radius of the displayed disk therefore tends to infinity. A compact set has finite maximal distance from the fixed center \(c(T)\), which proves enclosure.

The argument proves eventual behavior on the larger sublevel. Pairwise non-migration at *all* times has been proved here under the smaller hypothesis \(d(0)\le4\). Whether a transient crossing of a line can occur when \(4<d(0)\le36\) remains open here. The final inclusion from the geometric margins already has an independent [Lean proof](../../Migration/DefectFourHull.lean); the defect decay and the eventual-enclosure argument in this note are written arguments.
