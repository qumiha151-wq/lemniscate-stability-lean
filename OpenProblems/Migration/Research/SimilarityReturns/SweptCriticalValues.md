# Swept critical values and signed multiplicity in a migration gap

Let \(X:S^1\times[0,T]\to\mathbb R^2\) be a smooth family of closed regular immersions. Choose positively oriented coordinates \((x,h)\). Assume
\[
 b=\max h(X_T)<a=\min h(X_0),\qquad B=\mathbb R\times(b,a).
\]
Write \(K=X(S^1\times[0,T])\). On a free elastic flow put \(F=k_{ss}+k^3/2\), \(N=JT\), \(X_t=-FN+\lambda T\), and \(ds=g\,du\) with \(g=|X_u|\). Its signed Jacobian in the domain orientation \((u,t)\) is \(-gF\). In particular a critical value has a preimage at which the elastic force vanishes.

## The two outermost points on each line are distinct stationary images

For every \(b<c<a\), the compact intersection \(K_c=K\cap\{h=c\}\) has two distinct horizontal extrema. Every preimage of either extremum has \(F=0\). If any preimage were regular, the inverse function theorem would put an open disk about the image into \(K\); neither time endpoint can give such a preimage.

To see that the extrema differ, suppose instead that \(K_c=\{p\}\), and put \(\tau=\inf\{t:\min h(X_t)<c\}\). At this interior time \(\min h(X_\tau)=c\). Every contact point in the parameter circle maps to \(p\). Its tangent is horizontal, so \(x_u\ne0\). These preimages are isolated and finite. Choose small disjoint neighborhoods on which \(x_u\) has fixed nonzero sign, whose boundary heights at time \(\tau\) exceed \(c\). These properties persist for sufficiently close times. Take times tending to \(\tau\) from above with \(\min h<c\). After extracting a subsequence the minimizing labels approach a contact label. At a selected such time there are intersections with \(h=c\) on both sides of the minimizing label in its neighborhood. Their horizontal coordinates are distinct, a contradiction.

In fact the diameter of \(K_c\) has a positive local lower bound as \(c\) varies in the gap. Suppose \(c_j\to c\in(b,a)\) and \(\operatorname{diam}K_{c_j}\to0\). For sufficiently large \(j\), \(K_{c_j}\ne\varnothing\), and after a subsequence its points converge uniformly to a single \(p\). Any point of \(\partial\{(u,t):h(X(u,t))<c\}\) in the domain at which \(h=c\) and which is approached also by points with \(h>c\), maps to \(p\), by the intermediate value theorem in arbitrarily small connected neighborhoods. To handle possible plateaus at \(c\), take one-sided subsequences. If \(c_j<c\), then **every** boundary point of \(\{h(X)<c\}\) maps to \(p\), by values below \(c\) arbitrarily near this point. If \(c_j>c\), reverse time and height. In the first case take the earliest time \(\tau\) when \(\{h<c\}\) accumulates. The compact set of labels at \(\tau\) where this accumulation occurs consists of preimages of \(p\); at each such label \(h=c=\min h(X_\tau)\), so \(x_u\ne0\). Take pairwise disjoint neighborhoods with \(x_u\ne0\) and with endpoints outside this finite accumulation set. For times sufficiently close to \(\tau\) their endpoints are never below \(c\). Choose such a time with a point below \(c\) in a selected neighborhood. The two endpoints of the component of \(\{u:h(X(u,t))<c\}\) there are distinct boundary points in spacetime. Both map to \(p\), contradicting strict monotonicity of \(x\) on the neighborhood. A subsequence with \(c_j=c\) is ruled out by the preceding exact-level result. Compactness now gives a uniform positive diameter on each compact subinterval of the gap.

## The physical zero-force image contains a continuum crossing each substrip

Fix \(b<d_1<d_2<a\), take \(M>\max_K |x|\), and let \(R=[-M,M]\times[d_1,d_2]\). Any material trajectory has a subpath in \(R\) joining top to bottom, by first taking its first hit of the bottom and its last preceding hit of the top. It meets every left-to-right path in this rectangle. In particular each such left-to-right path must meet \(\partial K\): it starts outside \(K\) and intersects \(K\). The closed set \(R\cap\partial K\) therefore contains a compact connected subset meeting both horizontal sides, by the rectangle crossing lemma. Every point on this continuum is a critical value by the inverse function theorem, since \(R\) avoids the two endpoint curves. [Pascoletti and Zanolin, crossing lemma](https://doi.org/10.1155/2013/267393)

The same yields a connected compact subset of \(K\cap\{b\le h\le a\}\) joining the full gap boundaries by Hausdorff subsequential convergence of these continua as \(d_1\downarrow b,\ d_2\uparrow a\). All points of the limit are images of force zeros, including the two edge heights: the zero set is compact in spacetime.

The continuum is in the physical plane. Pure sweep topology cannot ensure that one connected component of the zero set in **parameter–time** spans the gap. To see the distinction for normal speed, move circles of radius one vertically from center height \(10\) to \(0\), then expand their radius smoothly to two at center height \(0\), then translate to center height \(-10\). Choose smooth monotone changes flat at the joining times, and strict expansion in the interior of the middle phase. Throughout an open interval in that phase the normal speed has no zero. Zero-speed components before this interval all have heights at least \(-2\); those after it all have heights at most \(2\). Thus no such component spans, for example, the closed substrip \([-5,5]\). This family prescribes circle-center motion and does not solve the free elastic flow. The PDE might impose more on its parameter–time zero set.

## Opposite elastic forces on the same slice inside every open substrip

For every regular value \(c\in(b,a)\) of \(h\circ X\), its inverse image is a finite collection of smooth circles in the interior of the parameter–time cylinder. At least one circle has nonzero degree under projection to the parameter circle. Indeed the oriented boundary of \(\{h(X)\ge c\}\) consists of the initial circle and these level circles with suitable signs. Their signed homology sum equals, up to the common orientation, the generator of the cylinder.

Every nonempty such level circle maps onto a nondegenerate compact horizontal interval. At a maximum of time along the circle its nonzero tangent vector is purely spatial. The derivative of \(X\) there is horizontal and nonzero by immersion. Thus the interval has positive length. By Sard's theorem and Fubini, \(A_B=|K\cap B|>0\), where area is ordinary two-dimensional Lebesgue measure.

**Theorem.** For every \(b<d_1<d_2<a\), there is a nonempty open interval of physical times in \((0,T)\) on which every slice contains a point with \(F>0\) and a point with \(F<0\), both strictly inside \(d_1<h<d_2\).

Choose a regular \(c\in(d_1,d_2)\) and a component of its preimage. Orient the component by the nonvanishing vector \((h_t,-h_u)\) in the \((u,t)\) cylinder. The horizontal-coordinate derivative in this direction is \(x_u h_t-x_t h_u=-gF\). Since the periodic horizontal coordinate is nonconstant, \(F\) takes both signs on this spacetime circle. Its time projection is a compact interval \(I\subset(0,T)\). At every \(t\in I\) some label reaches \(c\), so the preimage of \(d_1<h<d_2\) on that slice is a nonempty open set of labels.

On each positive-time slice \(F\) is real analytic in arclength, as proved below. The dilation first variation \(\int F(X-p)\cdot N\,ds=-E<0\) excludes \(F\equiv0\) on the connected closed slice. Thus it cannot vanish on that nonempty open set of labels. The subsets of \(I\) on which a point in the open substrip has \(F>0\), respectively \(F<0\), cover \(I\). Both are relatively open and nonempty, the latter assertion coming from the chosen level circle. By connectedness they intersect. At a time in the intersection fix one label of each strict sign. Continuity preserves the strict signs and the strict height bounds on a common open interval about that time. This proves the theorem. The time interval may depend on the chosen substrip.

## Spatial analyticity of the force at every positive time

Use fractional arclength \(y\in\mathbb R/\mathbb Z\) and the clock \(d\tau=L^{-4}dt\). Put \(U=Lk\), \(f=U_{yy}+U^3/2=L^3F\), and \(v=\int_0^1Uf\,dy\). In fractional-arclength coordinates the position evolves by \(X_\tau=L(-fN+wT)\). Differentiating \(|X_y|=L\) gives \(L_\tau/L=w_y+Uf=v\). A time-dependent shift of the arclength origin adds its time derivative to the mean of \(w\); choose it so that \(w\) is the mean-zero primitive of \(v-Uf\). The tangent angle has time derivative \(-f_y+Uw\), and its \(y\)-derivative is \(U\). Hence
\[
 U_\tau+\partial_y^4U=P(U),\qquad
 P(U)=-\tfrac52U^2U_{yy}-3U(U_y)^2-\tfrac12U^5+vU+wU_y .
\]
The angle derivatives are periodic for every turning number. These geometric formulas only use smoothness and a smooth positive length on the chosen compact time interval.

For \(r\ge0\), \(j=0,2\), let \(A_r^j\) be the periodic Fourier space with norm
\[
 \|z\|_{A_r^j}
   =\sum_{n\in\mathbb Z}(1+|n|)^j e^{r|n|}|\widehat z(n)|,
 \qquad z(y)=\sum_n\widehat z(n)e^{2\pi i n y}.
\]
The inequality \(e^{r|n+m|}\le e^{r|n|}e^{r|m|}\) gives the Banach algebra estimate in \(A_r^0\). The first two derivatives map \(A_r^2\) boundedly into \(A_r^0\) with uniform constants. Taking the mean has norm at most one; division of each nonzero Fourier coefficient by \(2\pi i n\), and setting the zero mode to zero, bounds the mean-zero primitive in \(A_r^0\). Thus \(U\mapsto v,w,P(U)\) are bounded and Lipschitz on each ball of \(A_r^2\) in the scalar or \(A_r^0\) target, with constants depending only on the radius of the ball. This follows by subtracting one factor at a time in their finite polynomial expressions. All constants are independent of \(r\).

Start at any normalized time \(\alpha\) and let \(r(\tau)=\tau-\alpha\). The multiplier \(S(q)=e^{-q\partial_y^4}\) from time \(\sigma\) to \(\tau=\sigma+q\) gains the weight \(e^{q|n|}\). After the weight gain its multiplier is \(e^{-q((2\pi n)^4-|n|)}\), which is at most one and, for \(n\ne0\), at most \(e^{-q|n|^4}\). Consequently
\[
 \|S(q)\|_{A_{r(\sigma)}^2\to A_{r(\tau)}^2}\le1,\qquad
 \|S(q)\|_{A_{r(\sigma)}^0\to A_{r(\tau)}^2}\le C(1+q^{-1/2}).
\]
The second estimate follows by taking the supremum of \((1+|n|)^2e^{-q|n|^4}\); its time singularity is integrable.

For completeness, take paths on \([\alpha,\alpha+H]\) for which the sequence \(e^{r(\tau)|n|}\widehat U(\tau,n)\) is continuous with values in the fixed weighted \(\ell^1\) space of norm \(\sum(1+|n|)^2|z_n|\). This is a Banach space with its supremum norm. The map
\[
 U(\tau)\longmapsto S(\tau-\alpha)U(\alpha)
       +\int_\alpha^\tau S(\tau-\sigma)P(U(\sigma))\,d\sigma
\]
uses fixed initial data on its right. It preserves the stated continuity. In weighted variables, products are convolutions with extra factors \(e^{r(|n|-|m|-|n-m|)}\) of modulus at most one, continuous in \(r\) by finite Fourier truncation and the uniform algebra bound. The conjugated semigroup is strongly continuous on the fixed space by dominated convergence. For the integral, the part within distance \(\varepsilon\) of its upper endpoint has norm \(O(\varepsilon+\sqrt{\varepsilon})\), and the rest is continuous by the multiplier formula. On a ball of radius \(R\) the integral term has bound and Lipschitz constant at most \(C_R(H+2\sqrt H)\), using the two estimates above. For \(\|U(\alpha)\|_{A^2_0}\le M\), take \(R=2M+1\), then choose \(H>0\) so that this map sends the ball to itself and has Lipschitz constant less than one. It has a unique fixed point.

The true smooth solution satisfies the same Duhamel formula coefficient by coefficient. On a compact smooth time slab its unweighted \(A^2_0\) norm has a uniform bound \(M\), for instance by bounding four spatial derivatives. In the unweighted continuous path space on the same short interval the identical contraction estimate holds, with weight zero, so the true solution and the weighted fixed point coincide there. The interval length \(H\) depends on this common \(M\) only. Given any positive time on the smooth flow, choose a compact normalized-time slab ending there and start the short construction less than \(H\) before its endpoint. At that endpoint \(U\in A_r^2\) for some \(r>0\); hence \(f\in A_r^0\) and its Fourier series is holomorphic on \(|\operatorname{Im}y|<r/(2\pi)\). The physical force \(F=L^{-3}f\) is real analytic in arclength on that slice. In particular its zeros are finite there, since it is nonzero somewhere by the dilation identity. This proof requires no analyticity of the initial immersion or of material parametrizations.

## Winding multiplicity and energy in the open gap

Write \(w_t(z)\) for the winding number of the oriented immersion \(X_t\) around \(z\) off its image. For almost every \(z\in B\), the signed sum of Jacobian signs over its preimages is zero: it is the boundary winding difference up to overall sign, and both endpoint winding numbers vanish there. So almost every point in \(K\cap B\) has a preimage of each Jacobian sign. In fact the two multiplicities are equal pointwise almost everywhere. The area formula gives
\[
 \int_{X^{-1}(B)} F_+\,ds\,dt
 =\int_{X^{-1}(B)} F_-\,ds\,dt\ \ge A_B>0,
\]
where \(F_\pm=\max(\pm F,0)\). The same sign balance holds over every measurable subset of \(B\). In the disjoint endpoint half-planes the absolute multiplicity is bounded below by the absolute endpoint winding number. Consequently
\[
 \|w_0\|_{L^1(\mathbb R^2)}+\|w_T\|_{L^1(\mathbb R^2)}+2A_B
 \le \int_0^T\int |F|\,ds\,dt
 \le \sqrt{(E(0)-E(T))\int_0^T L(t)\,dt}.
\]
This applies also to self-intersecting or multiply covered slices. Using the absolute winding avoids cancellation across different regions. The plus and minus gap contributions have separately positive dissipation. More quantitatively, if \(M_\pm=\int_{X^{-1}(B)\cap\{\pm F>0\}} ds\,dt\), Cauchy–Schwarz gives \(\int_{X^{-1}(B)}F^2 ds\,dt\ge A_B^2(M_+^{-1}+M_-^{-1})\).

**Both endpoint winding terms can be taken strictly positive, including at turning number zero.** At every positive time the spatial arclength parametrization of the immersion itself is real analytic. Indeed the tangent is obtained from a local tangent-angle lift by integrating the analytic curvature and taking sine and cosine; integrating the unit tangent gives the immersion. On its arclength parameter circle the subgroup of position periods is closed and proper by regularity, hence finite. Divide out this subgroup to obtain a primitive analytic unit-speed immersion \(\gamma\) of some period \(\ell>0\). Write \(d\ge1\) for the number of traversals of \(\gamma\) in the original slice.

The primitive immersion has finitely many pairs of distinct parameter points with the same position. Compactness and local injectivity give a uniform neighborhood of the diagonal free of such pairs. If there were infinitely many pairs, they would thus accumulate at two distinct labels \(s_*,s_*'\) with equal position. If the two tangents there are transverse, the inverse function theorem isolates the pair. For parallel tangents, use the common tangent direction as a local horizontal axis. Both regular image arcs are analytic graphs over this axis. Infinitely many approaching pairs give infinitely many distinct horizontal intersection coordinates because each local projection is injective. The two analytic graphs coincide on an interval. On that interval two arclength parametrizations are related by \(s\mapsto \varepsilon s+c\), \(\varepsilon\in\{1,-1\}\). Analytic continuation of the two position maps on \(\mathbb R\) now yields \(\gamma(s)=\gamma(\varepsilon s+c)\) everywhere. For \(\varepsilon=1\) this gives a nontrivial period modulo \(\ell\); for \(\varepsilon=-1\), differentiation at \(c/2\) gives \(\gamma'(c/2)=-\gamma'(c/2)\). Both violate primitivity or regularity, respectively.

Choose a point on \(\gamma\) with a unique primitive preimage. In a sufficiently small disk about it, the trace is one embedded arc, with all other parts excluded by compactness. The oriented winding jumps by one across that primitive arc, and by \(d\) in absolute value for the original slice. At least one open side therefore has nonzero winding, so \(\|w_t\|_1>0\) for every positive \(t\). If strict migration is specified starting at the original smooth time zero, compact uniform continuity allows replacing that time by a sufficiently small positive \(\varepsilon\) while keeping strict separation from the terminal slice and, if prescribed, retaining any given compact substrip of the original gap. Applying the cost inequality to \([\varepsilon,T]\) then makes both endpoint winding terms strictly positive. It gives a lower bound for the dissipation on that shortened physical interval.

One independent lower estimate on this gap expenditure uses normal material labels. Put \(m_*=\int_{S^1}\min_{0\le t\le T}|X_u(u,t)|\,du>0\). Each label crosses the whole strip, so integration of the derivative of its height clamped to \([b,a]\) gives \(\int_{\{b<h<a\}} |h_t|\,dt\ge a-b\) for that label. Since \(|h_t|\le|F|\) in this gauge, the two equal signed expenditures in the open gap are each at least \((a-b)m_*/2\). This depends on material compression of the single flow.

There is no estimate here making the strictly positive swept-area costs exceed the available energy for every genuine trajectory. Nor does the argument construct a genuine migrating flow. The existence question of [Miura and Wheeler](https://arxiv.org/abs/2404.12619) therefore remains open. These are mathematical proofs and do not have a Lean formalization here.
