# A common physical disk from initial bending alone

Let \(X\) be a smooth, closed, immersed planar free elastic flow. Write \(E=\tfrac12\int k^2\,ds\), \(L=\int ds\) and \(c=L^{-1}\int X\,ds\). Suppose \(s\) is a time in its smooth time interval, and that
\[
2E(s)L(s)\le4\pi^2+\tfrac{11}{2}.
\]
For each later \(t\) in that interval,
\[
\overline B\!\left(c(s),\,\tfrac{846}{1000}\tfrac{\pi}{E(s)}
                         +\tfrac4{1000}\tfrac{\pi}{E(t)}\right)
\subseteq \operatorname{conv}X(t).
\]
Consequently all subsequent hulls contain the same closed disk,
\(\overline B(c(s),\,\tfrac{85}{100}\pi/E(s))\). Its radius is strictly positive. The bound on \(2EL\) is imposed at one time. The orientation can be chosen arbitrarily. [Initial-data theorem](../../Migration/SublevelPhysicalDisk.lean) · [Fixed disk](../../Migration/SublevelFixedRadius.lean)

The arclength parametrization of an actual material slice gives a closed Frenet curve. For that curve put \(F=k_{ss}+k^3/2\). On \(4\pi^2<2EL\le4\pi^2+36\), its turning integral equals one of \(\pm 2\pi\), and
\[
E\int kF\,ds<L\int F^2\,ds .
\]
Each identity is verified in the Migration project. Writing \(E'=-\int F^2\,ds,\ L'=\int kF\,ds\) now gives a strictly negative derivative at every threshold \(4\pi^2<C\le4\pi^2+36\) of \(2EL\). A closed-set argument propagates the non-strict initial inequality even when the initial value equals \(C\). [Spatial rate](../../Migration/SublevelSpatialRate.lean) · [Transfer and propagation](../../Migration/SublevelMaterialInvariant.lean)

The turning integral is continuous and stays in \(\{-2\pi,2\pi\}\) on this sublevel. If positive initially, the positive-turn time-slab theorem applies at once. For negative turning, complex conjugation reflects the position, tangent and hull, reverses signed curvature and signed normal force, and preserves the flow equation, length and bending. Reflection maps the resulting disk back to its original physical center. Finally, \(E(t)\le E(s)\) gives the fixed radius. [Time-slab estimate](TimeSlab.md) · [Reflection](../../Migration/SublevelReflection.lean)

This excludes migration for the stated range of initial bending. Whether there is a migrating smooth flow outside that range remains a separate question.
