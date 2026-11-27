# A common disk on an actual low-bending time interval

Suppose a smooth closed planar immersion moves by free elastic flow on a time interval containing \([s,t]\). Write \(E=\frac12\int k^2ds\), \(L=\int ds\), \(R=\pi/E\), and let \(c\) be the arclength centroid. Assume that throughout \([s,t]\) the signed turn is \(2\pi\) and \(2EL\le4\pi^2+11/2\). Then
\[
\overline B\bigl(c(s),\,0.846R(s)+0.004R(t)\bigr)
 \subseteq \operatorname{conv} X(t).
\]
The corresponding disk at \(s\) and the disk at \(t\) overlap at the earlier centroid, so the two entire curves cannot lie on opposite sides of a line. This Lean theorem has hypotheses only on the immersion, its physical velocity equation, bending energy and signed turn on the time interval. [Physical theorem](../../Migration/LowDefectMaterialSlab.lean)

At one time write \(D=(2EL-4\pi^2)/(4\pi^2)\) and identify the plane with the complex numbers. Use the centered position \(G=(2\pi/L)(X-c)\) and its unit tangent in fractional arclength. The Fourier modes outside \(0,1,2\) contribute at most \(0.575\sqrt D\) to the uniform position error. The bound follows by pairing the two integer frequency tails, summing an explicit telescoping rational majorant and applying Cauchy–Schwarz to finite sums before passing to the limit. The second mode contributes at most \(0.133D\). The Fourier series of this actual position converges absolutely, and its pointwise sum recovers the original curve. Maximizing its first harmonic gives a genuine point of support in every physical direction. [Position series](../../Migration/LowDefectPositionSeries.lean) · [Directional support](../../Migration/LowDefectMaterialSupport.lean)

The previously verified normal-position correction has squared mean at most \(0.75^2D\). Combining it with the position supremum bounds the arclength-centroid flux using the physical centroid, normal, and actual scalar curvature. Integration of the force and energy identities then gives the disk above. [Material flux estimate](../../Migration/LowDefectMaterialFlux.lean)

The initial-data version uses propagation of the bending sublevel and orientation. The independent Migration theorem stated here assumes the sublevel on the time interval. [Initial-data argument](LowDefectPhysicalDisk.md)

