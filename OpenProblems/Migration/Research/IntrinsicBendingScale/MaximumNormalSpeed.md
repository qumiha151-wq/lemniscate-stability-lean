# Time integrability of the maximum physical speed

Let \(\gamma(t,u)\) be any global smooth closed planar free elastic flow in normal material labels. Write \(M=\max |k|\), \(D=\int (k_{ss}+k^3/2)^2ds\), and \(E=\frac12\int k^2 ds\). Every integer \(j\ge0\) admits a constant \(C_j\) independent of length, multiplicity and initial data such that for \(S>0\)
\[
 \int_S^\infty\|\partial_s^j k(t)\|_\infty^{6/(j+1)}\,dt
 \le C_j\big[S^{-1/2}+E(S/2)^2-E_\infty^2\big]. \tag{1}
\]
Here \(E_\infty=\lim E(t)\). Every one of these curvature derivatives tends to zero uniformly in space. In particular the real normal speed \(F=k_{ss}+k^3/2\) satisfies \(\int_0^\infty\|F\|_\infty^2\,dt<\infty\). Smooth initial data supply the finite contribution near zero. For every \(t\ge s\) and every material parameter \(u\),
\[
 |\gamma(t,u)-\gamma(s,u)|^2\le(t-s)\int_s^t\|F(v)\|_\infty^2\,dv. \tag{2}
\]
Consequently every material point remains within \(o(\sqrt t)\) of its initial position, uniformly over the entire curve. The implied rate may depend on the individual flow. A closed flow whose centroid diverges can satisfy this estimate.

## Uniform interior smoothing from local bending

Use the normalization, weights and notation of the [local bending theorem](IntrinsicBendingScale.md). On its common time interval the unit-interval \(L^2\) norms of \(V'=Y_{xx}\) are uniformly bounded and \(1/2\le |V|\le2\). We show that at any fixed positive interior time all spatial derivatives are bounded independently of the initial higher derivatives and period.

Fix \(n\ge2\), put \(U_n=\int\omega_y|V^{(n)}|^2\) and \(B_n=\int\omega_y|V^{(n+2)}|^2\). In the parabolic equation \(Y_t=-aV'''+H\) integrate twice by parts:
\[
 \tfrac12 U_n'=\int(\omega_y V^{(n)})''\partial_x^{\,n-1}(-aV'''+H).
\]
The principal term is \(-\int a\omega_y|V^{(n+2)}|^2\). Each remainder is a bounded smooth coefficient of \(V\) times a weight bounded by \(C\omega_y\) times differentiated \(V\) factors. If the weight is undifferentiated, there are \(m\ge3\) factors of positive orders \(d_i\) and \(\sum d_i=2n+4\). If a derivative falls on the weight, \(m\ge2\) and \(\sum d_i\le2n+3\). At most one factor has order \(n+2\), and all others have order at most \(n+1\). On each unit interval put a highest-order factor in \(L^2\) and the others in \(L^{2(m-1)}\). Interpolating on the triple interval between the bounded local \(L^2\) norm of \(V'\) and the \(L^2\) norm of \(V^{(n+2)}\) costs high-norm exponent
\[
 \sum_i\frac{d_i-1+1/2-1/p_i}{n+1}
   =\frac{\sum_i d_i-m/2-1}{n+1}<2.
\]
Young's inequality, comparability of the weights on triples and finite overlap give \(U_n'+c_n B_n\le C_n\). This includes all differentiated coefficients because \(a\) is smooth on the metric annulus and \(H\) has total derivative order three with at least two differentiated factors. No large-scale periodic Sobolev constant enters.

The same one-dimensional interpolation with \(p=2\), followed by concavity in summing the unit-interval weights, gives
\(U_n\le C_n(1+B_n^{(n-1)/(n+1)})\).
Consequently
\[
 U_n'\le C_n-c_n U_n^{(n+1)/(n-1)},\qquad
 U_n(\tau)\le C_n(1+\tau^{-(n-1)/2}).
\]
The latter follows by integrating the differential inequality above the fixed level where its negative term is at least twice its constant term. This bound holds independently of \(U_n(0)\). Uniform local Sobolev embedding and \(1/2\le |V|\le2\) now control each curvature derivative at every interior time. Arclength differentiation is \(g^{-1}\partial_x\), with \(g=|V|\).

Return to the physical scale. There is a universal \(\alpha>0\) and, for each \(j\), a constant \(b_j\ge1\) such that
\[
 M(v)\le r^{-1}\quad\Longrightarrow\quad
 Q_j(v+\eta r^4)\le b_j/r,\qquad
 Q_j(t)=\|\partial_s^j k(t)\|_\infty^{1/(j+1)},\quad \alpha\le\eta\le2\alpha. \tag{3}
\]
Choose \(2\alpha\) strictly below the universal existence time. The physical \(Q_j\) depends only on the image with its intrinsic arclength and is unaffected by the gauge change.

For the pointwise decay, use \(R=\min(s/2,\kappa/(E(s/2)^2-E_\infty^2)^2)\) as in the local bending theorem, decreasing universal \(\kappa\) as necessary. The static stress estimate gives \(\int_{s-R}^{s-R/2}M^6\le2^{23}(E(s/2)^2-E_\infty^2)\). At some \(v\) in that interval, \(M(v)\le[2^{24}(E(s/2)^2-E_\infty^2)/R]^{1/6}\). Take \(r^4=R/(2\alpha)\). The definition of \(R\) then gives \(rM(v)\le1\), and \((s-v)/r^4\in[\alpha,2\alpha]\). Equation (3) yields \(Q_j(s)\le C_jR^{-1/4}\). Since \(R\to\infty\), the claimed uniform decay follows.

## Distribution of high-speed times

For a level \(\lambda>0\), set \(r=b_j/\lambda\) and \(\Delta_\lambda=\alpha b_j^4\lambda^{-4}\). The contrapositive of (3) at \(\eta=\alpha\) gives, at every \(t\ge\Delta_\lambda\),
\[
 Q_j(t)>\lambda\quad\Longrightarrow\quad
 M(t-\Delta_\lambda)>\lambda/b_j .
\]
Translation of time preserves measure. If \(\Delta_\lambda\le S/2\), the entire corresponding past lies in \([S/2,\infty)\). If \(\Delta_\lambda>S/2\), discard the initial interval \([S,S/2+\Delta_\lambda]\), of length at most \(\Delta_\lambda\), and then use the same translate. Therefore
\[
 |\{t\ge S:Q_j(t)>\lambda\}|
 \le |\{v\ge S/2:M(v)>\lambda/b_j\}|
       +\Delta_\lambda\mathbf1_{\{\Delta_\lambda>S/2\}}.
\]
These continuous time functions have measurable superlevel sets. Integrate against \(6\lambda^5 d\lambda\). The first term contributes \(b_j^6\int_{S/2}^\infty M^6\). The second contributes
\[
 6\alpha b_j^4\int_0^{(2\alpha b_j^4/S)^{1/4}}\lambda\,d\lambda
 =3\sqrt2\,\alpha^{3/2}b_j^6 S^{-1/2}.
\]
The closed-curve stress inequality \(M^6\le2^{24}ED\), together with \((E^2)'=-2ED\), proves (1). Taking \(j=0,2\) bounds \(\int\|F\|_\infty^2\). The material velocity equation \(\partial_t\gamma=-FN\), the fundamental theorem of calculus and Cauchy–Schwarz prove (2). To see uniform subdiffusive displacement from the initial slice, split at a fixed \(S\). The initial finite displacement divided by \(\sqrt t\) vanishes as \(t\to\infty\); the rest divided by \(\sqrt t\) has limsup at most \((\int_S^\infty\|F\|_\infty^2)^{1/2}\). Now let \(S\to\infty\).

## Material acceleration

In pure-normal material labels the Frenet evolution equations give \(\partial_t T=-F_sN\), \(\partial_t N=F_sT\), \(\partial_t k=-F_{ss}-k^2F\), and \([\partial_t,\partial_s]=-kF\partial_s\). Give \(\partial_s^i k\) weight \(i+1\). Since \(F\) has weight three, differentiating a differential monomial in material time raises its weight by four. It follows that \(\gamma_{tt}=-F_t N-F F_s T\) is a finite sum of tangent and normal terms with scalar monomials of weight seven. For such a monomial apply Hölder to its \(6/7\) power with exponent \(7/(i+1)\) on each factor of weight \(i+1\), counting multiplicities. Equation (1) bounds every resulting integral by the same tail bound up to a fixed constant. Thus
\[
 \int_S^\infty\|\gamma_{tt}\|_\infty^{6/7}dt
 \le C[S^{-1/2}+E(S/2)^2-E_\infty^2].
\]
All curvature derivatives tend to zero. Consequently the maximum acceleration eventually stays below one, giving \(\int_0^\infty\|\gamma_{tt}\|_\infty dt<\infty\) for smooth initial data. The material velocity has finite total variation, uniformly over the original fixed label circle, and converges in its supremum norm to zero.

## Width cost of a separated pair

Suppose the whole image at \(s\) has strictly smaller height than the whole image at \(t\) in some unit direction; denote the directional widths by \(W_s,W_t\) and the positive separating gap by \(d\). At an initial label of minimum height the projected displacement is at least \(W_s+d\). At the terminal label of maximum height it is at least \(W_t+d\). Thus
\[
 (\max(W_s,W_t)+d)^2\le(t-s)\int_s^t\|F(v)\|_\infty^2\,dv.
\]
Either endpoint satisfying (1) of the local bending theorem at radius \(r\) has \(W\ge r/2\). This gives an independent physical cost based on either endpoint, including \(r=M^{-1}\). In particular the gap together with the larger width is \(o(\sqrt{t-s})\) uniformly for any sequence of separated pairs with \(s\to\infty\). These estimates leave the existence of such a pair open.

The independent Migration Lean module proves (2) for any continuous envelope of the actual force on the slab and the strict half-plane lower bounds separately from the intrinsic curvature of the initial and of the terminal slice. On a fixed compact slab the true maximum of \(|F|\) is continuous by compactness of the fixed parameter circle; clamping its time argument extends the envelope continuously to all real times. The weighted higher-derivative estimates, the distribution-function proof and unconditional tail integrability are analytic results in this note.
