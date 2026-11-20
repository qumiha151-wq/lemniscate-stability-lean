# Circular convergence from a signed curvature moment

Consider a smooth closed immersed planar free elastic flow for all \(t\ge0\). Use arclength \(ds\), signed curvature \(k\), force \(F=k_{ss}+k^3/2\), and the normal velocity \(-FN\). Define

\[
B=\int k^2\,ds=2E,\quad C=\int k^3\,ds,\quad
D=\int F^2\,ds,\quad U=LE,\quad
G=\frac{\sqrt L\,|C|}{B^{3/2}}.
\]

**Theorem.** If \(G(t)\ge1\) for all sufficiently large times, then the turning number \(n\) is nonzero. After division by length the flow converges smoothly up to reparametrisation to the \(|n|\)-covered circle, and
\[
\lim_{t\to\infty}\frac{L(t)^4}{t}=32\pi^4 n^4.
\]
This applies if at each sufficiently late time either \(k\ge-\tfrac12\sqrt{B/L}\) everywhere or \(k\le\tfrac12\sqrt{B/L}\) everywhere. In particular it applies if curvature eventually has one sign on each slice. Immersions with self-intersections are allowed.

**Length growth below the circularity threshold.** Write \(S=\int k\,ds=2\pi n\), constant under regular homotopy. If \(G\ge g>1/2\) eventually, then quarter-power length growth holds and
\[
\limsup_{t\to\infty}2E(t)L(t)\le \frac{S^2}{(2g-1)^2}.
\]
In particular every turning-zero flow satisfies \(\liminf_{t\to\infty}G(t)\le1/2\). If \(G\ge1/2\) eventually then \(L(t)=O(t^{1/4}(1+\log t))\). If \(0<g<1/2\) and \(G\ge g\) eventually, then
\[
 E(t)=O\!\left(t^{-g/(1+2g)}\right),\qquad
 L(t)=O\!\left(t^{1/(2+4g)}\right).
\]
A positive limiting bending energy would thus require \(\liminf G=0\).

## First variations and length growth

Periodicity gives \(\int F\,ds=C/2\). The actual flow satisfies \(L'=\int kF\,ds\) and \(E'=-D\). Cauchy–Schwarz gives \(|L'|\le\sqrt{BD}\) and \(D\ge C^2/(4L)\). Moreover \(B>0\) by closure and \(D>0\) by the dilation first variation \(E=-\int F\langle\gamma,N\rangle ds\). [Miura and Wheeler, §§2–3](https://arxiv.org/html/2404.12619v3)

For \(s\le t\) the first variations and Cauchy–Schwarz in time give
\[
 |L(t)-L(s)|^2\le(t-s)\int_s^t 2E D\,du=(t-s)(E(s)^2-E(t)^2).
\]
In particular \(L(t)\le L(0)+E(0)\sqrt t\). Wirtinger's inequality on the mean-zero unit tangent gives \(2EL\ge4\pi^2\), so \(\log(E(T)/E(t))=O(1+\log(1+t))\) for fixed \(T\).

For \(t\ge T\) with \(G(t)\ge g>0\) use the clock \(\xi=\log(E(T)/E(t))\). It is strictly increasing and diverges. Indeed \(\sqrt D\ge g B^{3/2}/(2L)\) gives \(L'/L\le D/(gE)\). If \(E\) had a positive limit this estimate would bound \(L\), and \(D\ge g^2B^3/(4L^2)\) would stay uniformly positive, contradicting the energy identity.

On each slice normalise length to one. Write \(b=LB\), \(c=L^2C\), \(d=L^5D\), \(v=L^3 L'=\int\hat k\hat F\), where hats refer to the unit period. Write \(\mu=c/2=\int\hat F\). The squared norm identity \(\int(2\mu\hat F-d)^2=d^2\), and Cauchy–Schwarz after multiplying by \(\hat k\), give
\[
  \frac{v}{d}\le\frac{\sqrt b+\operatorname{sgn}(c)S}{|c|}.
\]
Indeed \(|2\mu v-dS|\le d\sqrt b\). Since \(d\log L/d\xi=bv/(2d)\) and \(G=|c|/b^{3/2}\), the quantity \(x=\sqrt b\) satisfies
\[
 \frac{dx}{d\xi}\le\frac{(1-2g)x+|S|}{4g}.
\]
When \(g>1/2\), integration gives \(\limsup x\le |S|/(2g-1)\) and a uniform upper bound on \(U=b/2\). When \(g=1/2\), it gives \(U=O((1+\xi)^2)\). For \(g<1/2\), it gives \(U=O(E^{-(1-2g)/(2g)})\).

At the endpoint \(g=1/2\), a flow of turning number zero has \(dx/d\xi\le0\). It thus has bounded \(U\) and the exact quarter-power upper estimate without a logarithmic factor. The energy decay and \(LE\ge2\pi^2\) also give the corresponding lower estimate \(L(t)\ge c\,t^{1/4}\) for all sufficiently large times.

To convert these estimates back to physical time, use \(-E'=D\ge 2g^2E^5/U^2\). A bounded \(U\) gives \(E=O(t^{-1/4})\). At \(g=1/2\), integrating \((E^{-4})'\ge c_1/(1+\log(1+t))^4\) gives \(E=O(t^{-1/4}(1+\log(1+t)))\). Below the threshold, integrate \(-E'\ge c_2 E^{3+1/g}\) to obtain the asserted power. The time-secant bound on successive intervals \([2^jT,2^{j+1}T]\) and the final partial interval gives the matching upper estimates for \(L\) by a geometric sum. If \(S=0\), the universal lower bound \(x\ge2\pi\) contradicts the limiting upper bound whenever \(g>1/2\).

## Rigidity at the threshold

Assume now \(G\ge1\) on the tail. Then
\[
 U'=E\int kF\,ds-LD\le E\sqrt{BD}-LD\le0.
\]
The scale-invariant product \(U\) is bounded below by \(2\pi^2\) (periodic Wirtinger on the unit tangent). Use the rescaled time \(d\tau=dt/L^4\); the quarter-power length bound just proved makes \(\tau\) unbounded. At each time normalise arclength to a unit period, so \(\hat k=Lk\), \(\hat F=L^3F\), \(\hat B=LB=2U\), \(\hat C=L^2 C\), and \(\hat D=L^5D\). On this unit interval the nonnegative dissipation is
\[
 -\partial_\tau U=\hat D-\tfrac12\hat B\int\hat k\hat F.
\]
Its time integral is finite. Choose \(\tau_j\to\infty\) along which it tends to zero. Write \(b_j=\hat B_j\), \(d_j=\hat D_j\), and \(c_j=\hat C_j\). We have \(0<4\pi^2\le b_j\le2U(T)\) and
\[
 0\le\sqrt{d_j}(\sqrt{d_j}-b_j^{3/2}/2)
 \le-\partial_\tau U(\tau_j)\longrightarrow0.
\]
Hence \(d_j\) is bounded, \(\sqrt{d_j}-b_j^{3/2}/2\to0\), and \(0\le d_j-c_j^2/4\to0\) because \(|c_j|\ge b_j^{3/2}\). In particular the \(L^2\) distance of \(\hat F_j\) from its mean \(c_j/2\) tends to zero. Also \(\sqrt{b_jd_j}-\int\hat k_j\hat F_j\to0\), by subtracting the preceding two nonnegative contributions to \(-\partial_\tau U\).

Here are the compactness details. With \(X_j=\|\hat k_j''\|_2\), integration by parts gives \(\|\hat k_j'\|_2^2\le\|\hat k_j\|_2 X_j\). Integrating the derivative of \(\hat k_j^2\) from a point where \(\hat k_j^2\le b_j\) gives \(\|\hat k_j\|_\infty^2\le b_j+2\sqrt{b_j}\|\hat k_j'\|_2\). The force equation gives \(X_j\le\sqrt{d_j}+\tfrac12\sqrt{b_j}\|\hat k_j\|_\infty^2\le K(1+\sqrt{X_j})\). Thus the curvatures are bounded in \(H^2\). Extract a subsequence converging in \(C^1\) to \(k_*\), and take \(c_j/2\to f_*\ne0\), using the lower bound on \(|c_j|\). Then \(\hat F_j\to f_*\) in \(L^2\). Passing to the limit in the second Cauchy–Schwarz deficit gives
\[
 \int k_* f_*=\|k_*\|_2\,|f_*|.
\]
Equality forces \(k_*\) constant. Preservation of signed turning identifies its value as \(2\pi n\), and the lower bound on \(b_j\) excludes \(n=0\). On these slices \(L^3\int k_s^2ds=\int|\hat k_j'|^2\to0\). Restart at one of these times and apply the circle stability theorem for the resulting nonzero turning number. Smooth length-normalised convergence gives \((L^4)'=4\int(\hat k^4/2-|\hat k'|^2)\to32\pi^4n^4\). Integration gives the claimed physical coefficient. [Miura and Wheeler, Theorem 1.2](https://arxiv.org/html/2404.12619v3#S1)

Finally set \(R=\sqrt{B/L}\). If \(k\ge-R/2\), integrating the nonnegative polynomial \((k+R/2)(k-R)^2\) gives \(C-LR^3\ge0\). Reversing the orientation gives the assertion for \(k\le R/2\).

There is also an explicit rate before any stability theorem is applied. In unit-length variables write \(K=b-S^2\) and \(\delta=-\partial_\tau U\). Expansion of the squares gives the exact identity
\[
 16\delta-b^2 K
 =\int(4\hat F-b\hat k-c)^2 + (bS-c)^2+2(c^2-b^3).
\]
Under \(G\ge1\), all three terms are nonnegative. As \(\partial_\tau K=-2\delta\), one obtains \(\partial_\tau K\le-b^2 K/8\). Therefore \(K(\tau)\le K(\tau_0)\exp[-2\pi^4(\tau-\tau_0)]\) using \(b\ge4\pi^2\). This estimate is in \(\tau=\int L^{-4}\,dt\).

## A gap below the circular value

For \(n\ne0\) there is a number \(g_n<1\) such that \(\liminf G>g_n\) implies convergence to the \(|n|\)-covered circle and convergence of the unscaled arclength centroid to a finite point. In particular the limit of \(G\) is then exactly one.

In fact let \(\varepsilon_{|n|}>0\) be the curvature-oscillation stability threshold and put \(g_n=(1+|S|/\sqrt{S^2+\varepsilon_{|n|}})/2\). Choose \(g\) strictly between \(g_n\) and \(\liminf G\). The preceding bound gives
\[
\limsup K_{\rm osc}=\limsup(2EL-S^2)
 \le S^2\big((2g-1)^{-2}-1\big)<\varepsilon_{|n|}.
\]
Restart at a time below the stability threshold and rescale that slice to length \(2\pi|n|\), reversing its orientation if necessary. The cited theorems give circular convergence and convergence of the physical centroid. The factor of two between the two normal-velocity conventions is a constant change of physical time. The normalised clock is unbounded because of the quarter-power upper bound. [Andrews and Wheeler, Theorems 1 and 2](https://arxiv.org/html/2509.11129v2)

These conclusions constrain trajectories with a non-negligible signed third moment. For unrestricted immersed trajectories that moment can cancel between arcs of opposite curvature.
