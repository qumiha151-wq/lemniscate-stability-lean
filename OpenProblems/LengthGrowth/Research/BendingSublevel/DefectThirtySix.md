# Fourth-root growth from the initial bending product

Let \(X\) be a smooth regular closed planar free elastic flow, \(L\) its length, \(k\) its signed arclength curvature, \(B=\int k^2\,ds\), and \(U=LB\). If \(U(0)\le 4\pi^2+36\), then \(U\) is nonincreasing and
\[
 L(t)\le\max\{2L(0), (4 U(0)^2 t)^{1/4}\}
\]
in the convention \(X_t=-FN\), \(F=k_{ss}+k^3/2\), modulo tangential reparametrization. At every noncircular slice in this sublevel the product derivative is strictly negative. The result concerns individual flows throughout their smooth lifetime. It provides a sufficient initial condition for the [length question of Miura and Wheeler](https://arxiv.org/abs/2404.12619). The [monotonicity result of Novaga, Proposition 3.1](https://arxiv.org/html/2611.07242v1#S3) gives a previous sufficient condition \(U(0)\le4\pi^2+8/3\).

## Turning number in the sublevel

Take an arclength tangent-angle lift \(\theta\) on \([0,L]\), with \(\theta(L)-\theta(0)=2\pi n\). If \(n\) is even, the unit vector \(S=(\cos(\theta/2),\sin(\theta/2))\) is periodic. Choose a unit vector \(e\) perpendicular to \(\int S\) and set \(h=e\cdot S\). Then \(\int h=0\). The double-angle identity and closure \(\int e^{i\theta}=0\) give \(\int h^2=L/2\). Since \(|h_s|\le|k|/2\), periodic Wirtinger gives \(B\ge 8\pi^2/L\). For odd \(|n|\ge3\), Cauchy gives \(U\ge4\pi^2 n^2\). Thus \(U\le4\pi^2+36<8\pi^2\) forces \(|n|=1\). Orient so that \(\mu=L^{-1}\int k=2\pi/L>0\).

## Necessary moments at a nondecreasing slice

Put \(D=\int F^2,\ J=\int kF,\ C=\int k^3,\ R=\sqrt{B/L}\). The physical identities are \(B'=-2D,\ L'=J\). At a slice with \(U'\ge0\) we therefore have \(2LD\le BJ\). The dilation identity has \(|\int F(X-c)\cdot N|=B/2\) for the arclength centroid \(c\). By centered periodic Wirtinger, \(\int|X-c|^2\le L^3/(4\pi^2)\), hence \(D\ge\pi^2B^2/L^3\) and \(J\ge\mu^2 B/2\). The variation and virial identities hold for arbitrary closed immersions. [Variation formulas and virial bound](https://arxiv.org/html/2611.07242v1#S2)

Set \(\lambda=B/(4L)\). Expansion of the square gives \(\int(F-\lambda k)^2\le\lambda^2 B\). Testing against the constant function, using \(\int F=C/2\), yields
\[
 C\le B(\mu+R)/2 .
\]

Write \(u=k-\mu,\ V=\int u^2,\ Q=\int u_s^2,\ I_j=\int u^j,\ d=U-4\pi^2\). Then \(V=d/L\). When \(V=0\) we have a circle. Otherwise set \(\sigma=R/\mu=\sqrt{1+d/(4\pi^2)}>1\). The cubic bound and \(B=L\mu^2+V,\ C=L\mu^3+3\mu V+I_3\) give
\[
 2\mu I_3\le\mu^2 V\big(\sigma+1/(\sigma+1)-5\big).
\]
Here \((\sigma^3-1)/(\sigma^2-1)=\sigma+1/(\sigma+1)\). Integration by parts gives \(J=-Q+\tfrac12\int k^4\). Expanding \(k^4\) and using the lower bound for \(J\) and the upper bound for \(I_3\) gives
\[
 Q+\big(\tfrac52-\sigma-1/(\sigma+1)\big)\mu^2 V\le I_4/2. \tag{1}
\]

## The one-dimensional inequality and the contradiction

Choose an arclength origin where \(u=0\), available by continuity and zero mean. Let \(G(s)=\int_0^s u^2\). Integration of \(((G-V/2)u^2)'\) gives \(I_4=-2\int(G-V/2)u u_s\). The cubic primitive yields \(\int(G-V/2)^2u^2=V^3/12\). Cauchy gives
\[
 3I_4^2\le V^3Q. \tag{2}
\]
Here \(Q>0\), since a constant mean-zero \(u\) is zero. For \(0<d\le36\), \(\pi>157/50\) gives \(\sigma<139/100\). The function \(z+1/(z+1)\) is increasing for \(z\ge1\). Thus (1) holds with coefficient \(c=69/100\) on the left. Combining (1), (2) and \((Q+c\mu^2V)^2\ge4c\mu^2VQ\) implies \(V^2\ge48c\mu^2\). But \(V/\mu=d/(2\pi)\le900/157\) and \((900/157)^2<48c\). This contradiction proves strict decrease at every noncircular slice of the sublevel.

## From one time slice to length growth

On the boundary \(U=4\pi^2+36\) the curve is noncircular, so \(U'<0\), including the right derivative at the initial time. A first-exit argument makes the sublevel forward invariant. Within it \(U'\le0\) everywhere, with \(U'=0\) on a circle. For \(E=B/2\), Cauchy and energy dissipation give \((L')^2\le2ED=-(E^2)'\). If \(L(t)>2L(0)\), continuity gives an earlier \(s\) with \(L(s)=L(t)/2\). Then \(L(t)/2\le E(s)\sqrt{t-s}\le U(0)\sqrt t/L(t)\), as asserted. Similarity preserves \(U\), so the strictness also gives a [closed-similarity rigidity consequence](../../../SolitonClassification/Research/LowBending/SimilarityRigidity.md).

## Mechanization boundary

Lean verifies the sharp fourth-moment interpolation from the fundamental theorem of calculus, Cauchy–Schwarz, and the choice of a zero for a periodic mean-zero curvature. It also verifies the centered moment algebra, the numerical constant, the contradiction, and the implication from the inward boundary derivative to fourth-root growth on the actual flow. The identification of all analytic hypotheses on the same slice, including the turning-number reduction, is provided by the written argument above. The unrestricted length question remains open in this project. [Sharp interpolation](../../LengthGrowth/ActualFlow/DefectSharpInterpolation.lean) · [Moment contradiction and flow-length implication](../../LengthGrowth/ActualFlow/DefectThirtySix.lean)
