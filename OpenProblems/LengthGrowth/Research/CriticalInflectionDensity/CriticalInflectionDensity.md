# Sharp dependence on the number of strong curvature reversals

Let a smooth periodic curvature \(k\) have period \(P>0\) and root-mean-square one. Write
\[
 \int_0^P k^2=P,\qquad f=k''+\tfrac12 k^3,\qquad D=\int_0^P f^2,\qquad d=D/P .
\]
Suppose the circle splits into \(n\ge1\) intervals so that on each interval either \(k\ge-1/2\) throughout or \(k\le1/2\) throughout. There is a universal \(C\) with
\[
 \boxed{\quad \sqrt d\ge\tfrac12-C\,n^{3/2}/P.\quad}                         \tag{1}
\]
Thus the pieces separate excursions above \(1/2\) from excursions below \(-1/2\) in RMS units. Infinitely many changes of sign of smaller amplitude are allowed. Every smooth slice has a finite such partition. Indeed \(M=\sup|k'|<\infty\) by periodicity, and on any subinterval of length at most \(1/(2M)\) the curvature differs from its initial value by at most \(1/2\); constant curvature needs only one piece. The formal index is the least \(N\) such that every subarc of length at most \(P\) uses at most \(N+1\) pieces. Cutting a cyclic partition at an arbitrary basepoint can split one piece. A curve with \(N>0\) genuine sign changes satisfies the cyclic hypothesis with \(n=N\). If \(k\) has one weak sign, \(\sqrt d\ge1/2\) holds exactly by integrating \(f\) and using Hölder.

The dependence in (1) is sharp for smooth closed immersed plane curves of turning number one. Below we construct slices with \(n\to\infty\), \(n^{3/2}/P\to0\), and \(1/2-\sqrt d\asymp n^{3/2}/P\). At \(n\asymp P^{2/3}\) the deficit can stay bounded away from zero. There are also sequences with \(n/P\to0\) and \(d\to0\).

## The tent estimate on an interval

It suffices to work with \(D<P/4\). Put
\[
 W=(k'^2+k^4/4)^{1/2},\quad A=\max(1,\sqrt{\max W}),\quad
 R=\int_0^P(|f|-1/2)^2,\quad J=\int_0^P|f|,\quad X=P/2-J.
\]
Then \(|k|\le\sqrt2 A\le2A\) and \(0\le R=D-J+P/4\le X\).

On a piece \(I=[a,b]\), choose \(\sigma=\pm1\) with \(u=\sigma k\ge-1/2\) and use the piecewise affine tent \(\phi(s)=\min(1,s-a,b-s)\). For \(a<b\), integrating by parts on its linear pieces gives \(\int_I\phi u''\ge-1-4A\). The endpoints contribute \(u(a)+u(b)\ge-1\), and the downward slope changes have total magnitude two, hence contribute at least \(-2\sup u\). For a short segment the tent has one slope change of magnitude two at its midpoint. A degenerate piece has zero integral.

Where \(\phi=1\), \(3u^2/2-u^3\le1/2\) by \((u-1)^2(u+1/2)\ge0\). On either ramp let \(r\) be distance to the adjacent endpoint, so \(0\le r\le1\) and \(\phi=r\). For \(-1/2\le u\le0\), \(3u^2/2-ru^3\le1/2\). For \(0\le u\le2A\), put \(e=1/(2A)\). Then \(eu^3\le u^2\) and
\[
 3u^2/2-ru^3\le3u^2-(r+e)u^3\le4/(r+e)^2 .
\]
The last inequality follows from \(((r+e)u-2)^2((r+e)u+1)\ge0\). Each ramp has integrated excess above \(1/2\) at most \(\int_0^1 4/(r+e)^2\,dr\le8A\). Thus \(\int_I\phi u^3\ge(3/2)\int_Iu^2-|I|/2-16A\). Combining this with \(u''+u^3/2=\sigma f\) and integration by parts yields
\[
 \tfrac32\int_I k^2\le2\int_I|f|+\tfrac12|I|+32A .
\]
Summing and using \(\int k^2=P\) proves
\[
                              0\le R\le X\le16nA.                              \tag{2}
\]

## The oscillation estimate bounds the largest stress

If \(A\ge2\), choose \(s_0\) where \(W(s_0)=A^2\) and put \(K(y)=k(s_0+y/A)/A\), so \(W_K(0)=1\). Write \(p=200(n+1)\). If \(p/A\le P\), the window splits into at most \(n+1\) excursion pieces because the cut can split one of the circle's pieces. On each, some sign \(\sigma\) has \(\sigma K\ge-1/(2A)\ge-1/4\). The rescaled force \(g=K''+K^3/2\) satisfies
\[
                                \int_0^p |g|>1/4.                              \tag{3}
\]
Otherwise \(|W_K'|\le|g|\) where \(W_K>0\) gives \(3/4\le W_K\le5/4\) by first passage, so \(|K|,|K'|\le2\). Integrating \((KK')'=W_K^2-3K^4/4+Kg\) gives \((3/4)\int K^4\ge9p/16-8-1/2\). On each excursion piece \(|K|^3\le\sigma K^3+1/32\). Integrating \(K''=g-K^3/2\) on each piece bounds \(\int|K|^3\le2\int|g|+8(n+1)+p/32\). Since \(K^4\le2|K|^3\), the two bounds contradict \(p=200(n+1)\).

Scaling (3) back and using (2),
\[
 A^2/4<\int_{s_0}^{s_0+p/A}|f|\le p/(2A)+\sqrt{pR/A}\le C n .
\]
If \(A<2\), the estimate \(A\le C\sqrt n\) is immediate. If \(A\ge2\) and \(p/A>P\), then \(A<p/P\le400n/P\). We need only treat \(P\ge n^{3/2}\), since otherwise (1) is trivial. Thus \(A\le C\sqrt n\) in all needed cases. Equation (2) now gives \(X\le Cn^{3/2}\), and \(J/P\le\sqrt d\) proves (1).

## Closed curves attaining the error

We give one construction that also realizes positive instantaneous growth of \(EL\). Choose a fixed smooth nonnegative envelope \(\eta\), supported on \([0,1]\), positive on \((0,1)\), equal to one on \([1/3,2/3]\), and flat at the endpoints. Let \(A\ge2\) be large and \(0\le\lambda\le1/4\). Let \(w\) solve
\[
 w''+w^3/2=(\lambda/A^2)w,\qquad w(0)=0,\quad w'(0)=1 .
\]
It is a smooth periodic oscillator with two simple zeros per period \(p_A\), and zero mean. Indeed \(w'^2+w^4/4-(\lambda/A^2)w^2=1\). If \(B>0\) is its turning amplitude, the squared speed factors as \((B^2-w^2)(B^2+w^2-4\lambda/A^2)/4\). Thus \(B\) is bounded above and below away from zero, and after substituting \(w=B\sin\theta\), the quarter-period is \(\int_0^{\pi/2}2(B^2+B^2\sin^2\theta-4\lambda/A^2)^{-1/2}d\theta\). This proves uniform upper and lower bounds for the period and the period mean of \(w^2\), together with uniform bounds on \(w,w'\). Symmetries of the autonomous equation give \(w(s+p_A/2)=-w(s)\).

Fix a sufficiently large constant \(K\). Choose the integer \(m\) nearest to \(K A^2(\int_0^1\eta)/p_A\), and set \(M=m p_A/(A\int_0^1\eta)\), so \(M=KA+O(1/A)\). On one packet put
\[
 q(s)=A\eta(s/M),\qquad \phi(s)=\int_0^s q,\qquad k=q\,w(\phi),
                         \qquad 0\le s\le M .
\]
The packet is smooth and flat at both endpoints. Its signed turning is \(\int_0^{mp_A}w=0\). If \(Q=\int_{\rm packet}k^2\), the central plateau and the period bounds give \(Q\asymp A^2 M\). Constants here and in the following estimates can be chosen independent of \(K\ge1\) and large \(A\). Its exact force decomposes as
\[
 f=\lambda\eta(s/M)^2 k+e,\qquad e=q''w+3qq'w',\qquad
 \|e\|_2^2\le C(A^2/M^3+A^4/M)\le C Q/K^2.                                 \tag{P1}
\]
For \(\lambda=1/4\) the leading term \(f_0=\lambda\eta^2 k\) has \(\|f_0\|_2\le\sqrt Q/4\). Also \(f_0^2-k f_0/2\le0\) everywhere and equals \(-k^2/16\) on the central plateau, which carries a fixed positive fraction of \(Q\). Cauchy–Schwarz in (P1), with \(K\) fixed sufficiently large, yields a constant \(c_0>0\) such that
\[
 \int_{\rm packet} f^2\le(1/4-c_0)Q,\qquad
 \int_{\rm packet}(f^2-kf/2)\le-c_0Q.                                         \tag{P2}
\]

Form a half-block with this packet, one fixed smooth nonnegative compactly supported curvature bump of integral \(\pi\), and a matched pair of smooth plateaux of height \(+1\) and \(-1\). Each plateau has variable flat length \(H\ge0\) and fixed smooth ramps linking it to zero. Their signed turning cancels. Add one straight portion of whatever length makes the half-block length equal to its \(\int k^2\). This required length is \(Q-M+O(1)>0\) and is independent of \(H\). Repeat the half-block twice. The resulting smooth curvature has mean square one and period \(P=2(Q+2H+O(1))\). Each half turns through exactly \(\pi\); hence the integrated unit tangent is anti-periodic over a half-block and the position closes. The turning number is one. The number of genuine sign changes satisfies \(N=4m+O(1)\asymp A M\).

The minimum number \(n\) of half-RMS excursion pieces also satisfies \(n\asymp AM\). It is at most \(N+1\). On the central packet plateau a fixed positive fraction of the \(m\) oscillator periods appear at amplitude \(A\), and alternating extrema there exceed both half-RMS thresholds. Each adjacent pair of opposite strong extrema requires a partition boundary.

Each unit of plateau length contributes \(1/4\) to \(D\) and \(1/2\) to \(V=\int kf\). The fixed ramps and bump have bounded cost. Therefore (P2) implies \(P/4-D\asymp Q\) and \(V/2-D\asymp Q\). For the fixed \(K\), \(Q\asymp n^{3/2}\). Consequently
\[
 \tfrac12-\sqrt{D/P}\asymp n^{3/2}/P,\qquad
 \frac{V/2-D}{P}\asymp n^{3/2}/P .
\]
With \(H=0\) one has \(n\asymp P^{2/3}\) and a positive deficit bounded away from zero. Taking \(H/Q\to\infty\) gives the matching order arbitrarily far into the low-density range. Taking instead \(\lambda=0,\ H=0,\ K\to\infty,\ A\to\infty\) in (P1) gives \(D/P=O(K^{-2}+Q^{-1})\to0\) while \(n/P\asymp A^{-1}\to0\). Thus no error tending to zero with \(n/P\) alone controls \(\sqrt d\).

## An invariant count using the turning of each lobe

A second version of (1) counts only connected components \(I\) of the nonzero-curvature set for which \(\Theta_I=\int_I|k|\,ds>1/4\). This quantity is the total turning angle on the lobe and is unchanged by spatial dilation. Write \(m\) for the number of those components. The right side of (1) remains valid with \(n\) replaced by \(m+1\). Pointwise height plays no role in this count.

If curvature has no zero, its one-sign estimate already gives \(\sqrt d\ge1/2\). Otherwise cut the circle at a zero. Its nonzero-curvature components form at most countably many disjoint intervals, each with zero curvature at both endpoints (for a component crossing a chosen cut, cut at one of its endpoints instead). For one such \(I\), write \(u=|k|\), \(M=\max_I u\), \(Y=\int_I (u')^2\), \(B_I=\int_Iu^2\), \(J_I=\int_I|f|\), \(\Theta=\int_Iu\), and \(\ell=|I|\). Integrating \((u^{3/2})'\) from an endpoint to a maximum and applying Cauchy–Schwarz gives
\[
 M^3\le \tfrac94\Theta Y,\qquad \int_I u^4\le M^3\Theta\le\tfrac94\Theta^2Y .
\]
Since \(k\) vanishes at both endpoints, \(\int_I kf=-Y+\frac12\int_Iu^4\). Therefore \(M J_I\ge(1-9\Theta^2/8)Y\). For a small-turn lobe with \(\Theta\le1/4\), these estimates give \(J_I\ge\frac14M^2/\Theta\). In particular
\[
 2J_I\ge\int_Iu^3\ge B_I^{3/2}/\sqrt{\ell}
                 \ge \tfrac32 B_I-\tfrac12\ell .                              \tag{4}
\]
The first step uses \(\int_Iu^3\le M^2\Theta\); the last is the tangent-line bound for \(t^{3/2}\) at one. This lobe costs no endpoint error. On a large-turn lobe the preceding tent estimate contributes at most \(32A\). We may sum over all components by countable additivity of the nonnegative integrals; \(\int k^2\) vanishes on the remaining zero set, while including it in the length and in \(J\) only weakens the inequality. We obtain \(R\le X\le16m A\), even if infinitely many small-turn components occur.

In the rescaled oscillator window, \(\Theta\) is unchanged. Apply the first inequality of (4) to all complete small-turn lobes. At most \(m+2\) other pieces need a derivative endpoint estimate, namely the large-turn components and the two possible partial lobes at the window ends. If \(\int|g|\le1/4\) then \(|K'|\le2\) on the window, so integrating the constant-sign equation on these pieces yields \(\int|K|^3\le2\int|g|+8(m+2)\). The same virial contradiction works for \(p=200(m+2)\). The width and stress argument after (3) proves the stated estimate with \(m+1\).

In the packet examples, the turning of each complete oscillator lobe is exactly \(\int_{\text{one lobe}}|w(\phi)|\,d\phi\) since \(\phi'=q\). This tends to \(\pi\) as \(\lambda/A^2\to0\), by the factored energy integral; for zero detuning the integral on a lobe is \(2\int_0^{\sqrt2} w/\sqrt{1-w^4/4}\,dw=\pi\). Hence \(m\asymp AM\) in the same examples. The \(3/2\) exponent is sharp also for this turning-angle count.

## Consequences for one evolving curve

For a physical slice of length \(L\), bending energy \(E=\frac12\int k^2\) and dissipation \(\mathcal D=\int(k_{ss}+k^3/2)^2\), rescale the curve until the curvature has mean square one. Then \(P=\sqrt{2EL}\ge2\pi\) and \(d=\mathcal D L^2/(8E^3)\). In particular, for some universal \(C\),
\[
 \sqrt{\frac{\mathcal D L^2}{2E^3}}\ge 1-C\,\frac{n^{3/2}}{\sqrt{EL}} .
\]
With \(U=EL\) and the clock \(\xi=\log(E(t_0)/E(t))\), \(E'=-\mathcal D\) and \(L'\le\sqrt{2E\mathcal D}\) give \(d\log U/d\xi\le(2\sqrt d)^{-1}-1\). On slices where \(n^{3/2}/\sqrt U\) is sufficiently small, \(d\sqrt U/d\xi\le C n^{3/2}\). For example, if \(n\le B U^\sigma\) on all sufficiently late slices with \(U\) above a fixed threshold, with \(0\le\sigma<1/3\), integration from the last threshold crossing gives
\[
 U^{(1-3\sigma)/2}\le C(1+\xi),\qquad
 L(t)\le C(1+t)^{1/4}\bigl(1+\log(2+t)\bigr)^{1/(1-3\sigma)} .
\]
Here \(\xi\le C+\frac12\log(1+t)\) by the physical secant inequality and \(U\ge2\pi^2\). At the last time \(s\) with \(L(s)=L(t)/2\), the same secant inequality gives \(L(t)^4\le16(t-s)U(s)^2\). Times with \(L(t)\) bounded need no doubling. A positive limiting energy would give bounded \(\xi,U,L\), contradicting the virial lower bound for \(\mathcal D\) and its time integrability.

More generally, if \(n=o(U^{1/3})\) along every late sequence with \(U\to\infty\), then for each \(\varepsilon>0\), \(d\log U/d\xi\le\varepsilon\) at all sufficiently high \(U\) on late slices. Threshold integration bounds \(U\le C_\varepsilon e^{\varepsilon\xi}\), giving \(E\to0\) and \(L(t)=O_\delta(t^{1/4+\delta})\) for every \(\delta>0\) by the same secant argument. Thus a genuine super-quarter-power trajectory must have a sequence of late slices with \(U\to\infty\) and \(n\ge cU^{1/3}\). The same conclusion holds for the number of lobes having total turning greater than \(1/4\). Infinitely many small sign changes alone do not meet these necessary conditions. The sharp examples above are distinct closed initial curves. They establish the sharpness of the single-slice estimate and of the instantaneous drift estimate, leaving long-time growth on a single general flow open.

## A two-parameter bound at low dissipation

On an arbitrary RMS-normalized scalar slice with \(d\le1/16\), the same proof gives
\[
 n\ \ge\ c\min\bigl(P,\ P^{2/3}d^{-1/6}\bigr).                               \tag{5}
\]
For \(d=0\) the minimum is understood to be \(P\). Indeed \(X\ge P/4\) by Cauchy–Schwarz, and \(X\le C n A\). If \(A<2\), then \(n\ge cP\). If the oscillator window does not fit, \(A<p/P\le Cn/P\), again giving \(n\ge cP\). In the remaining case apply Cauchy–Schwarz directly to the force cost (3),
\[
 A^2/4<\int_{s_0}^{s_0+p/A}|f|\le\sqrt{(p/A)Pd}.
\]
This gives \(A^5\le CnPd\) and then \(P^4\le C n^6 d\). The same derivation works for the turning-angle lobe count (using \(m+1\)) and for the alternating groups in the companion proof, which supplies both \(X\le CnA\) and the corresponding window cost.

For actual closed immersed curves, the virial inequality \(\mathcal D L^3/E^2\ge4\pi^2\) gives the precise lower bound \(dP^2=\mathcal D L^3/(4E^2)\ge\pi^2\). Hence \(P^{2/3}d^{-1/6}\le\pi^{-1/3}P\), and (5) implies
\[
                         n^6 d\ \ge\ cP^4\qquad(d\le1/16).                     \tag{6}
\]
The packet with \(\lambda=0,\ H=0,\ K=A\to\infty\) has \(M\asymp A^2,\ P\asymp A^4,\ n\asymp A^3\). Formula (6) in this section and the packet force estimate above give \(d\asymp A^{-2}\); both parameters in (6) occur at matching order on actual closed curves.

At the critical count rate, assume \(n\le B U^{1/3}\) on late high-product slices of one flow. Then \(d\ge d_B>0\) there by (6) or \(d>1/16\); on the remaining bounded products the virial gives a positive lower bound as well. Put \(K=\max(1,1/(2\sqrt{d_B}))\), decreasing \(d_B\) if necessary to cover all late slices. The variation estimate gives \(d\log L/d\xi\le K\) and \(L\le C E^{-K}\). Thus \(E'=-8dE^3/L^2\le-cE^{3+2K}\), which implies \(E(t)=O(t^{-1/(2K+2)})\). At a last length doubling \(L(s)=L(t)/2\), the secant gives \(L(t)^2\le4(t-s)E(s)^2\le C t L(t)^{-2/K}\). Consequently \(L(t)=O(t^{K/(2K+2)})\), with exponent strictly below \(1/2\).

Finally suppose \(E_\infty>0\). Then \(L\to\infty\): otherwise disjoint unit intervals starting at uniformly bounded lengths would have bounded length throughout by the secant estimate, and the virial would contradict \(\int\mathcal D<\infty\). In the clock \(d\zeta=E^2L^{-2}\,dt\), the secant bound \(L=O(\sqrt{1+t})\) gives \(\int d\zeta=\infty\) while \(\int d\,d\zeta=\frac18\log(E(t_0)/E_\infty)<\infty\). Equation (6) therefore implies that for every fixed \(H\) the set of late times with \(n/P^{2/3}\le H\) is contained in a set of finite \(\zeta\)-measure. In particular there are late slices on this same flow with \(n/U^{1/3}\to\infty\).

For the half-RMS count, Lean verifies the static estimate (1), the finite minimum index, the physical normalization, and the closed-curve low-dissipation bound (6). The bound (6) has an explicit constant in `CriticalLowDissipationMaterial.lean`. The flow theorems verify the subcritical logarithmic rates, the necessary late sequence of reversals for failure of a quarter-plus-epsilon power bound, and the critical-count polynomial length and energy rates. The matching examples, the angular-count estimates and the frequency statement in the divergent clock have analytic proofs in this note and its companion. [Alternating groups of large-turning curvature arcs](AlternatingAngularGroups.md) · [Critical and logarithmic count criteria](OsgoodCriticalCount.md)
