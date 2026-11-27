# Circle rigidity at each nonzero turning number

Let a smooth closed immersed plane curve have length \(L\), signed curvature \(k\), and integer turning number \(n=(2\pi)^{-1}\int k\,ds\ne0\). Assume it is a self-similar solution of the free elastic flow. Its infinitesimal similarity may include translation, rotation and dilation. Define
\[
 B=\int k^2\,ds,\qquad M=2\pi|n|.
\]

If \(\sqrt{LB}\le M+3/5\), its unit-speed position has the exact form
\[
 X(s)=O+A\exp(iKs),\quad A\ne0,\quad KL=2\pi n.
\]
Thus it is a circle traced exactly \(|n|\) times with the prescribed orientation. The upper boundary is included. Equivalently, every noncircular closed self-similar solution of nonzero turning number obeys the strict separation
\[
 LB-(2\pi n)^2 > \frac{12\pi}{5}|n|+\frac9{25}.
\]

## Proof

Write \(E=B/2\) and \(F=k_{ss}+k^3/2\). The periodic similarity equation gives \(\int k F\,ds=aL\) and \(\int F^2\,ds=aE\), with \(a\) the dilation coefficient. In particular
\[
 E\int k F\,ds=L\int F^2\,ds .
\]

For an arbitrary closed unit-speed curve, put \(P=\sqrt{LB}\) and \(S=|\int k\,ds|\). Cauchy–Schwarz gives \(S\le P\). The spatial estimate in `MulticoverSlice.lean` proves that \(6\le S<P\le S+3/5\) implies
\[
 E\int kF\,ds<L\int F^2\,ds .
\]
The estimate uses the two spatial derivatives of the actual curvature. After normalizing to a period \(P\) with \(\int u^2=P\), the two arcs joining a maximum and minimum of \((u-1)^2\) control its oscillation. The signed inequality follows for both orientations. The integral identity for a similarity profile therefore forces \(P=S\), since \(S\ge2\pi>6\). Equality gives \(\int(k-L^{-1}\int k)^2\,ds=0\). Curvature is constant by continuity, and the Frenet equations yield the displayed position formula. The pure translation case is excluded by the closed-curve force identities.

The standalone Lean entry is `ClosedSimilarity.ClosedUnitFrenetCurve.multicover_all_similarity_generators` in `SolitonClassification/MulticoverCircles.lean`. It takes the signed turning, the initial curvature integral bound, and the actual position-force law. Each other ingredient is derived in this project.

Miura and Wheeler previously proved circle rigidity under their geometric stability condition. Andrews and Wheeler obtained smooth convergence for sufficiently small scale-invariant curvature oscillation at each covering number. The theorem here gives the explicit sublevel displayed above and a position formula. Closed self-similar profiles with arbitrary curvature are still unclassified. [Miura–Wheeler, §1.2](https://arxiv.org/html/2404.12619v3#S1.SS2) · [Andrews–Wheeler](https://arxiv.org/html/2509.11129v2)

