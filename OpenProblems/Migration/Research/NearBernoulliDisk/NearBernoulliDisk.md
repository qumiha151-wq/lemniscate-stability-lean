# An expanding disk common to all slices near a covered Bernoulli lemniscate

Fix a positive integer \(M\). Every sufficiently small, smooth perturbation of the \(M\)-fold expanding Bernoulli lemniscate in the curvature distance of the supplied stability manuscript has a fixed point \(p_0\) about which its convex hull contains an expanding disk at all physical times. This includes perturbations that differ between lobes and between the \(M\) traversals.

Let \(\ell_M\) be the reference \(M\)-cover length at maximum radius one, \(a=L(0)/\ell_M\), and \(\rho(t)=(a^4+30t)^{1/4}\). Write \(D=\mathcal K_M(\gamma_0)\). This is \(\ell_M\) times the squared \(L^2\) arclength distance from the signed curvature of \(a^{-1}\gamma_0\) to that of the reference, minimized over shifts of the reference parameter. There is a constant \(C_M\) and an initial neighborhood, chosen so that \(C_M\sqrt D<1/(2\sqrt2)\), for which

\[
 \overline B\!\left(p_0,\rho(t)\left[\frac1{2\sqrt2}-C_M\sqrt D\right]\right)
 \ \subseteq\ \operatorname{conv}\gamma(t),\qquad t\ge0 .
\]

The disk with \(\rho(t)\) replaced by \(a\) belongs to every hull. Consequently no two slices of such a flow can be strictly separated by a line. Every compact subset of the plane is eventually contained in all later hulls. If \(r(t)\) denotes the largest radius at the same \(p_0\), then
\[
        r(t)/\rho(t)\ \longrightarrow\ 1/(2\sqrt2).
\]
The limiting constant is exact, including on the reference itself. This is a corollary about the stability neighborhood. Migration for arbitrary initial closed immersions remains open.

## Reference disk and perturbation estimate

In its original parameter the reference has horizontal and vertical coordinates
\(\cos u/(1+\sin^2u)\) and \(\sin u\cos u/(1+\sin^2u)\).
Put \(r_B=\sqrt2/4\). All four points \((\pm\sqrt3 r_B,\pm r_B)\), with independent signs, belong to the image: take \(|\sin u|=1/\sqrt3\) and choose the signs of sine and cosine accordingly. Their rectangle contains the centred disk of radius \(r_B\). Conversely the entire image satisfies \(y\le r_B\). Indeed, \((1+\sin^2u)^2-8\sin^2u\cos^2u=(1-3\sin^2u)^2\ge0\). Hence the horizontal supporting line \(y=r_B\) proves optimality. Traversal multiplicity leaves these image statements unchanged.

At one fixed time let \(K\) be a compact physical image and let a normalized image be within \(\delta\) of the reference after applying a rotation, translating by \(p_0\), and scaling by \(\rho>0\). Precisely, every point of either physical image is within \(\rho\delta\) of some point of the other. A matched parametrization with uniform normalized error \(\delta\) implies this in both directions. Unit directional support values about \(p_0\) then change by at most \(\rho\delta\). Each support of the rotated reference is at least \(\rho r_B\), and one is exactly \(\rho r_B\). Intersecting the supporting half-planes of the compact convex hull gives
\[
        \rho(r_B-\delta)\le r(K,p_0)\le\rho(r_B+\delta)
        \qquad(0\le\delta<r_B).
\]
This reasoning permits the rotation and parametrization to change at every time.

## Analytic input and verification scope

The analytic input is the corollary “Orbital stability for all normalized times” in the supplied English TeX manuscript, together with its local-stability theorem. The corollary bounds the aligned normalized \(H^2\) shape error, up to rotation, by a constant times \(\sqrt D\). Sobolev embedding on the fixed reference period gives the needed \(C^0\) estimate, absorbing its norm into \(C_M\). The physical reconstruction in that manuscript uses a single translation \(p_0\) fixed when aligning the initial curve. This is the centre used throughout the disk conclusion. Long-time convergence after the same centering makes the normalized error tend to zero. The two-sided estimate above also transfers each applicable \(C^0\) rate in the stability theorem to \(|r(t)/\rho(t)-r_B|\).

The supplied file is identified by SHA-256 \(\texttt{7dabc635e25ac3dc3f29cf95f7a089191da3a4abbf4ff76758d11a26d1ad2247}\). The original formal project documents the global modulated solution, the physical graph and its identification with given flows. Its root records a different TeX revision with SHA-256 \(\texttt{2ff24714af447ae5641d9889284e3cf21755b4bfe662831238909463b8e07e6c}\). These sources supply the stability context for this geometric implication. [Original formal project and theorem index](https://github.com/qumiha151-wq/lemniscate-stability-lean/blob/main/Lemniscate.lean) · [Physical graph theorem](https://github.com/qumiha151-wq/lemniscate-stability-lean/blob/main/Lemniscate/BernoulliPhysicalGraphStability.lean) · [Given-flow identification](https://github.com/qumiha151-wq/lemniscate-stability-lean/blob/main/Lemniscate/LemniscateGivenFlow.lean)

The independent Migration project verifies the four-point support lower bound and exact upper supporting line directly from the trigonometric profile. It verifies both sides of the physical disk estimate, exact optimality on the reference, equality of the images of every positive cover, the fixed disk and exclusion of strictly separated slices at arbitrary nonnegative times, and convergence of the actual normalized centred inradius. The theorem \(\texttt{near_bernoulli_all_times}\) takes the all-time normalized shape estimate as a hypothesis. The Migration audit covers the geometric implication, while the stated small-curvature-to-orbital-estimate step uses the separately supplied stability theorem. [Reference geometry](../../Migration/BernoulliDisk.lean) · [Physical hull implications](../../Migration/BernoulliPerturbation.lean) · [Integrated audit](NearBernoulliDiskVerification.json)
