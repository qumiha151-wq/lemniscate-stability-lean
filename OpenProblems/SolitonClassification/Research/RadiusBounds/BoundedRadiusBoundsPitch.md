# Every centred radius cap bounds the rotation of noncircular expanders

Normalize the dilation coefficient to one. Given any finite \(H>0\), there is \(B_H<\infty\) such that every **noncircular** closed planar similarity expander with its whole image in the disk \(|X|\le H\) about its similarity centre satisfies \(|b|\le B_H\). Consequently a sequence of noncircular closed solutions with unbounded absolute rotation coefficient must escape all such disks along a subsequence. A sequence with \(|b|\to\infty\) has radius tending to infinity. There is no restriction on the full geometric period, covering or winding. A circle admits every \(b\), since the rotation only changes its parametrization.

We use the support quantities and exact radius balance from [the uniform-gap proof](UniformRadiusGapAllPitches.md). In particular \(R=\max|X|\ge R_*=2^{-1/4}\), \(c=1/R^2\), and
\[
 K=(X\cdot W+cq)/b-H_{\rm tor},\qquad
 H_{\rm tor}=qv-pk^2/2-k,\qquad b K'=\mathcal A-\varepsilon ,
\]
\[
 \mathcal A=(k+cp)^2/2+(1+c^2/2)(R^2-p^2)+b^2q^2,\qquad
 0\le\varepsilon=R^2-1/(2R^2)\le H^2 .
\]
All uses of periodicity are on the full closed immersion or its periodic extension. The proof is by contradiction. After a reflection take \(b\to+\infty\) and keep \(R\le H\) fixed as an upper bound. Below constants may depend on \(H\). The stress-window inequality with \(|F|\le(1+b)H\) gives \(|v|\le Cb,\ |k|\le C\sqrt b\).

## Uniform bounds on all moving windows

On the full period, or any physical interval of length at least \(b\) with \(\overline{\mathcal A}\le H^2\), the means of \(k^2,\,(bq)^2,\,v^2/b^2\) are bounded. For the last term integrate \(v^2=(kv)'+k^4/2-kF\) and use \(k^4\le Cb k^2\). The boundary contribution to \(\overline{v^2}\) vanishes on a period and is at most \(Cb^{3/2}/b\) otherwise. There is consequently one point of each such interval (or each full period) where all three quantities are bounded by a fixed constant. At this point
\[
 K=(qk^2/2+pv+cq)/b-(bq)(v/b)+pk^2/2+k
\]
is bounded in absolute value by a constant \(C_0(H)\).

In fact \(K\) is uniformly bounded **everywhere**. Should its range exceed the interval \([-C_0-H^2-2,C_0+H^2+2]\), it contains an interval of width at least \(H^2+1\) disjoint from \([-C_0,C_0]\), by the full-period good point. Periodicity gives a downward traversal of this interval staying inside it. It takes at least \(b\) units of arclength since \(K'\ge-H^2/b\), and \(\overline{\mathcal A}\le\varepsilon\) there by integration. This contradicts the good-point bound just established.

The integrated identity on *every* interval \(I_s=[s,s+b]\) now gives \(\int_{I_s}\mathcal A\le Cb\). Hence \(\int_{I_s}q^2\le C/b\). The pointwise bound \(|q'|=|1+kp|\le C\sqrt b\) gives \(\|q\|_\infty\le C b^{-1/6}\), by integrating on a one-sided interval over which \(|q|\) remains above half its starting value. In the slow coordinate \(y=(s-s_0)/b\), uniformly for arbitrary origins \(s_0\),
\[
 Q(y)=bq(s),\qquad (r^2)_y=2Q,\qquad r=|X|,\qquad
 \int_{j}^{j+1} Q^2\,dy\le C\quad (j\in\mathbb R).
\]
Thus \(r^2\) is uniformly Hölder continuous with exponent \(1/2\) on slow intervals of length at most one.

## Curvature away from the centre

For every fixed \(r_0>0\) we prove the uniform statement
\[
       \sup_{\{r\ge r_0\}}\left|k+\frac{1}{p}\right|\longrightarrow0 .
       \tag{1}
\]
Here eventually \(|p|\ge r_0/2\), by \(p^2=r^2-q^2\).

First \(\sup_{\{r\ge r_0\}}|k|=o(b^{1/3})\). If it failed, take \(s_0\) with \(r(s_0)\ge r_0\) and \(A=|k(s_0)|\ge\eta b^{1/3}\). One may move a distance at most \(2/A\) to a point \(s_1\) of curvature magnitude \(M\ge A\) where \(|k|\le2M\) on \([s_1-1/M,s_1+1/M]\). Indeed, if this bound fails, move within \(1/M\) to a point with more than doubled magnitude and repeat; strict doubling must terminate by boundedness on each periodic curve and the distances form a geometric series. On the resulting interval \(h(x)=k(s_1+x/M)/M\) satisfies \(|h|\le2,\ |h(0)|=1,\ \|h''+h^3/2\|_\infty\le(H+b\|q\|_\infty)/M^3=o(1)\). Bounded \(h,h''\) on \([-1,1]\) bound \(h'\) on \([-1/2,1/2]\) by an absolute constant (integrate Taylor's formula on a fixed half-interval). Thus on a fixed short subinterval starting at zero \(h\) keeps its sign and has magnitude at least \(1/2\). Take the subinterval so short that the net angle stays below one radian. The two endpoint tangents then have a difference bounded below independently of \(b\). But their physical separation in arclength tends to zero; \(r\ge r_0/2\) and \(p\) keeps its sign there. The identity \(X=qT+pN\) with \(q=o(1)\) makes \(N\) uniformly close to \(\operatorname{sgn}(p)X/|X|\), whose endpoint difference tends to zero. This contradiction proves the local \(o(b^{1/3})\) bound.

Now take any point \(s_0\) with \(r(s_0)\ge r_0\) and let \(P=p(s_0)\). On \(|s-s_0|\le1\), \((r^2)'=2q=o(1)\), and therefore \(r\ge r_0/2\) and \(\sup |p-P|=o(1)\), uniformly in \(s_0\). In the fast coordinate \(x=b^{1/3}(s-s_0)\), write \(u(x)=k(s)\). Differentiating the similarity equation gives, exactly,
\[
 (D_x^3+P)(u+1/P)=-(p-P)u+qu/b-\tfrac12 b^{-2/3}D_x(u^3).
\]
For \(r_0/2\le |P|\le H\), its whole-line inverse has kernels \(G_P,G'_P\) decaying exponentially with uniform rates and constants, by partial fractions at the three simple roots of \(z^3+P\). Choose \(\mu>0\) strictly below the common decay rate. Convolution by either kernel is bounded on the weighted sup norm \(\|g\|_\mu=\sup_x e^{-\mu |x|}|g(x)|\), because \(e^{-\mu|x|+\mu|y|}\le e^{\mu|x-y|}\). The globally bounded periodic \(u\) satisfies the convolution identity, with the differentiated cubic term paired with \(G'_P\).

Set \(V=\|u+1/P\|_\mu\). For \(|x|\le b^{1/3}\), the coefficient \(|p-P|+|q|/b+b^{-2/3}|u|^2=o(1)\) by the local bound just proved. Therefore the weighted norm of each undifferentiated input, or of \(b^{-2/3}u^3\) before pairing with \(G'_P\), on that region is at most \(o(1)(V+C)\). On its complement the weighted norm of these inputs is at most \(C(1+b)^2e^{-\mu b^{1/3}}\), using the global stress estimate. It follows that \(V\le o(1)(V+C)+o(1)\), proving (1) by evaluation at \(x=0\).

## The corrected radius and exclusion of passages through the centre

Set \(\Xi=r^2/2+v/b\). Since \((r^2)'=2q\) and \(v'=-k^3/2-p-bq\), the exact identity is
\[
                         b\Xi'=-p-k^3/2 .
\]
For any fixed \(r_0>0\), one also has \(\sup_{r\ge r_0}|v|/b\to0\). Indeed on a physical unit neighbourhood of any such point, \(r\ge r_0/2\) eventually and (1) gives uniformly bounded curvature. The curvature equation there gives \(|k''|\le C(1+b)\). Taking a forward Taylor difference on an interval of length \(b^{-1/2}\) bounds \(|v|\le C\sqrt b\). Thus on every fixed annulus bounded away from zero we have \(\Xi=r^2/2+o(1)\) and \(b\Xi'=-p+1/(2p^3)+o(1)\), uniformly.

Take \(r_1=R_*/4,\ r_2=R_*/2\). We show eventually \(\min r>r_1\). Otherwise, since \(\max r\ge R_*\), a connected component of \(\{r>r_1\}\) reaches \(r_2\) and returns to \(r_1\) at its next endpoint. Such a component exists by closed periodicity. The sign of \(p\) stays fixed throughout because \(q\to0\) uniformly. One crossing of \([r_1,r_2]\) goes from the lower radius to the upper one and another goes back down, staying in the annulus on each chosen crossing. On this annulus eventually \(r_1/2\le |p|\le r_2<R_*\), so \(-p+1/(2p^3)\) has the sign of \(p\) with magnitude bounded away from zero. If \(p>0\), \(\Xi\) is increasing on the descending radius crossing; its endpoint approximation by \(r^2/2\) requires it to decrease by \((r_2^2-r_1^2)/2+o(1)\). If \(p<0\), \(\Xi\) is decreasing on the ascending crossing with the opposite contradiction. This proves the lower bound on \(r\).

The entire curve now has \(r\ge r_1\), so \(p\) never vanishes and keeps a single sign. Formula (1) holds uniformly on the whole curve, with \(|1/p|\ge 1/H\). Thus \(k\) has one strict sign for all sufficiently large \(b\), and the periodic one-sign rigidity theorem identifies the centred circles. This contradicts the choice of noncircular profiles and proves the assertion.

The same theorem and the stress-window estimate imply pointed \(C^\infty_{\rm loc}\) subsequential compactness of the extended arclength **support** trajectories of noncircular profiles inside a fixed centred disk, even when the periods diverge. If the full periods remain bounded, frame and position closure pass to the limit as described in [the period-cap analysis](PrimitiveLimitsAndFourierReduction.md). Under unbounded periods the pointed limit is a complete bounded solution and need not inherit geometric closure. The proof here is analytic. The exact corrected-radius derivative, radius potential identity and critical-radius rigidity are kernel-checked in the associated [Lean module](../../SolitonClassification/RadiusPotential.lean).
