# A fixed disk in the convex hull of near-round free elastic flows

Let \(X\) be a smooth closed immersed planar free elastic flow, with normal material velocity \(-FN\), \(F=k_{ss}+k^3/2\). Denote its arclength centroid by \(B(t)=L(t)^{-1}\int X\,ds\), its energy by \(E=\tfrac12\int k^2\,ds\), and its turning number by \(n\). The dimensionless curvature oscillation is
\[
 \mathcal O=L\int(k-2\pi n/L)^2\,ds.
\]

**Theorem.** Suppose \(n\ne0\) and \(\mathcal O\le1/64\) on a time interval \([t_0,t_1]\). At every \(t\) in that interval the convex hull of the curve contains the closed disk of centre \(B(t_0)\) and radius \(L(t)/(4\pi|n|)\). In particular, a disk of this fixed centre and radius \(\pi |n|/(2E(t_0))\) lies in the hull throughout the interval.

There exists a universal \(\delta_0>0\), independent of the turning number, such that \(\mathcal O(0)\le\delta_0\) implies the disk conclusion for all nonnegative times. A smooth closed immersion of turning number zero has \(\mathcal O=2EL\ge4\pi^2\), so it cannot satisfy this small initial condition.

## Shape relative to the instantaneous centroid

Reverse orientation if needed and put \(S=2\pi |n|\). At a fixed time parametrize by unit fractional arclength \(x\in\mathbb R/\mathbb Z\), set \(Y=(X-B)/L\), \(K=Lk\), and integrate with respect to \(dx\). Then \(Y_x=T\), \(N_x=-KT\), \(\int Y=0\), \(\int N=J\int T=0\), and \(\int K=S\). Let \(a=1/8\), so \(\|K-S\|_2\le a\). The vector \(Z=Y+N/S\) has zero average and \(Z_x=(1-K/S)T\). Consequently
\[
 \|Z\|_\infty\le\int |Z_x|\,dx\le a/S,
 \qquad \|Y\|_\infty\le(1+a)/S.
\]
The first inequality follows by subtracting the mean and integrating differences over the period. The unit normal covers the unit circle because its degree is nonzero. In every direction the support value of \(Y\) is therefore at least \((1-a)/S\). The convex hull thus contains the disk of centre \(B(t)\) and radius \(L(t)(1-a)/S\).

There is also a direct way to obtain the required normal value which the
formal proof uses. Maximize \(e\cdot X\) for a unit vector \(e\). The
maximizer has \(e\cdot T=0\), hence \(e\cdot N=\pm1\), and its height is
at least \(e\cdot B(t)\) by the centroid formula. The positive sign would
give \(e\cdot Z\ge1/S>a/S\), so the sign must be negative. This argument
does not require a topological assertion about the Gauss map as an input.

## Displacement of the arclength centroid

Put \(D=\int F^2\,ds\) and \(U=EL\). The stress \(Q=k^2T/2+k_sN\) satisfies \(Q_s=FN\). Integrating this identity alone and after multiplication by \(X-B\) yields
\[
 \int FN\,ds=0,\qquad \int F(X-B)\cdot N\,ds=-E.
\]
The physical energy and arclength satisfy \(E'=-D\) and \(\partial_t ds=kF\,ds\). Differentiating the centroid using the first stress identity gives
\[
 B'=\frac1L\int F k(X-B)\,ds
    =\frac1L\int F[k(X-B)+N]\,ds .
\]
The squared mean of \(k(X-B)+N\) is \(\|K Y+N\|_2^2\). Its norm is at most
\[
 q=\|K-S\|_2\|Y\|_\infty+S\|Z\|_\infty
 \le a\left(1+\frac{1+a}{S}\right).
\]
Hence \(|B'|\le q\sqrt{D/L}\). The dilation identity and \(|X-B|\le (1+a)L/S\) give \(E\le (1+a)L^{3/2}\sqrt D/S\), or equivalently
\[
 \sqrt{D/L}\le\frac{1+a}{S}\,U\,\frac{D}{E^2}.
\]
The equality \(2U=S^2+\mathcal O\) bounds \(U\) between \(S^2/2\) and \((S^2+a^2)/2\). Integrating \(D/E^2=(1/E)'\) from \(t_0\) now proves
\[
 |B(t)-B(t_0)|\le
 \frac{L(t)}{S}\,a(1+a)
 \left(1+\frac{1+a}{S}\right)
 \left(1+\frac{a^2}{S^2}\right).
\]
For \(S\ge1\), \(a=1/8\), the last expression is at most \((L(t)/S)(1/8)(9/8)(17/8)(65/64)<3L(t)/(8S)\). Subtracting it from the instantaneous inradius leaves at least \(L(t)/(2S)\) about \(B(t_0)\). Finally \(L(t)\ge S^2/(2E(t))\ge S^2/(2E(t_0))\) yields the fixed physical radius asserted in the theorem.

## An initial condition independent of the turning number

Normalize the flow to length \(S\), so its mean curvature is one and \(e=\int(k-1)^2\,ds=\mathcal O/S\). The time changes, spatial dilations and factor of two in the speed convention preserve \(\mathcal O\). Proposition 4 of Andrews and Wheeler gives, whenever \(e\le1\),
\[
 e'\le -Q(f)+C\sqrt e\left(\int f_{ss}^2\,ds+e\right),\qquad
 Q(f)=\int(4 f_{ss}^2-10 f_s^2+8 f^2)\,ds,\quad f=k-1,
\]
with one constant \(C>0\) for all positive turning numbers. The elementary polynomial inequality \(x^4+1\le2(4x^4-10x^2+8)\) and Fourier series give \(\int f_{ss}^2+e\le2Q(f)\). Thus \(e'\le-Q(f)/2\) whenever \(e\le e_*:=\min\{1,(4C)^{-2}\}\). [Andrews and Wheeler, Proposition 4 and Corollary 8](https://arxiv.org/html/2509.11129#S2)

Take \(\delta_0=\min\{1/64,\pi e_*\}\). Since \(S\ge 2\pi\), the initial hypothesis gives \(e(0)\le e_*/2\). A first-crossing argument gives \(e(t)\le e(0)\) for the entire normalized lifetime. Returning to the physical flow gives \(\mathcal O(t)\le1/64\) at all times. The value of \(C\) enters only in this passage from a single initial slice to all later times. The theorem on a specified time interval uses the explicit oscillation threshold \(1/64\) directly.

The general half-plane migration question for closed free elastic flow remains open. [Miura and Wheeler, Section 1.2](https://arxiv.org/html/2404.12619v3#S1.SS2)
