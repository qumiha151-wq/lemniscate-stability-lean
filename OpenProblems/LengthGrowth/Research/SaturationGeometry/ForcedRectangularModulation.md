# Velocities of a rectangular elastica in a weak intermediate-scale limit

Write \(J(x,y)=(-y,x)\). A smooth free elastic flow has normal velocity \(-F\), where \(F=k_{ss}+k^3/2\). At a curvature scale \(H\), use current arclength \(x=Hs\), time \(\theta=H^2(t-t_0)\), \(K=k/H\) and \(G=F/H\). In the arclength chart about a material origin the equations are
\[
 K_{xx}+K^3/2=H^{-2}G,\qquad K_\theta=-G_{xx}+(\alpha K)_x,\qquad \alpha_x=-KG,\quad \alpha(\theta,0)=0 .
\]
The result below identifies the remaining normal velocity when the first equation tends to the rectangular-elastica equation. It applies without a proportionality relation between \(G\) and \(K\).

## Weak velocity classification on the whole spatial line

Let \(I\) be an open time interval and \(1\le p<\infty\). On \(I\times\mathbb R\) assume \(K\in L^3_{\rm loc}\), \(G\in L^p_{\rm loc}\), \(KG,\alpha,\alpha K\in L^1_{\rm loc}\), with
\[
 K_{xx}=-K^3/2,\qquad K_\theta=-G_{xx}+(\alpha K)_x,\qquad \alpha_x=-KG
 \tag{1}
\]
in distributions. Suppose on each compact time interval \(I'\Subset I\),
\[
 \liminf_{R\to\infty} R^{-(p+1)}
      \int_{I'}\int_{-R}^{R}|G|^p\,dx\,d\theta=0 .                    \tag{2}
\]
Then \(K\) either vanishes throughout \(I\), or it has one fixed, strictly positive oscillator amplitude throughout \(I\). In the latter case, in a fixed canonical frame, there is a time-dependent vector \(d\) such that
\[
 -G=d\cdot N,\qquad
 \int_{x_0}^{x_0+P_K}\omega(|K|)KG\,dx=0                              \tag{3}
\]
for almost every time, every \(x_0\), and every bounded Borel function \(\omega\). Here \(P_K\) is the minimal curvature period and \(N\) is the normal of the canonical unit-speed curve defined below. On a nonzero time interval, (1) alone allows in addition a dilation velocity and a rotation velocity. Condition (2) excludes both. For \(p=2\) the threshold in (2) is cubic.

### Time parameters and canonical curve

Let \(U''=-U^3/2,\ U(0)=0,\ U'(0)=1\). Its conserved quantity \(U'^2+U^4/4=1\) gives a periodic solution of period \(P>0\), with \(U(s+P/2)=-U(s)\). These facts follow by separation up to the finite positive turning point and reflection by uniqueness. Since \(U\) has zero mean, it has a bounded periodic second primitive. Every nonzero solution of the spatial equation is uniquely \(a U(ax+\phi)\), with \(a>0\) and \(\phi\) taken modulo \(P\). Indeed its conserved quantity equals \(a^4\), and the initial point and derivative traverse the corresponding connected energy oval once in a period. The spatial equation in (1) first gives \(W^{2,1}_{\rm loc}\) and then smoothness on almost every time slice.

For each fixed bounded spatial interval, after multiplying by an interior cutoff, the second equation in (1) gives an absolutely continuous representative in \(H^{-3}\) in time. In one dimension the supremum of the first two spatial derivatives of a test is bounded by its \(H^3\) norm. The representatives agree on overlapping windows. If \(a\to0\), then \(aU(ax+\phi)\to0\) uniformly. If \(a\to\infty\), testing and integrating twice against the periodic second primitive gives an \(O(1/a)\) distributional limit of zero, uniformly in phase. Therefore near any time with a nonzero representative the amplitudes stay in a compact subset of \((0,\infty)\). Compactness in phase and uniqueness show that the parameter map is continuous there, and every such time slice is an oscillator. This also shows that the nonzero times form an open set.

The parameters are locally absolutely continuous on that set. Indeed the two parameter derivatives are \(U(ax+\phi)+axU'(ax+\phi)\) and \(aU'(ax+\phi)\). They are linearly independent as spatial functions. An identity on an open interval extends analytically to the line, and subtracting its period translate first eliminates the amplitude coefficient and then the phase coefficient. Choose two smooth compactly supported tests whose pairings with those two derivatives have nonsingular matrix. The ordinary inverse function theorem expresses local lifts of \((a,\phi)\) as smooth functions of the two pairings, which are absolutely continuous in time by (1).

Set
\[
 C(y)=\left(U(y),\,\int_0^y U(z)^2/2\,dz\right),\qquad
 \widehat X(\theta,x)=a^{-1}C(ax+\phi),\quad T=\widehat X_x,\quad N=JT .
\]
The first integral gives \(|T|=1,\ T_x=KN\). The tangent is periodic and \(C(y+P)=C(y)+D_0\) for \(D_0=(0,\int_0^P U^2/2)\ne0\).

### Reconstruction from the weak equations

On any compact nonzero time patch set \(\widehat B=T_\theta\cdot N\). The parameter regularity just proved makes this a locally integrable time function with smooth spatial dependence. Differentiating \(T_x=KN\) gives \(\widehat B_x=K_\theta\) distributionally. Set \(B=-G_x+\alpha K\). Equation (1) gives \(B_x=K_\theta\), hence \(B-\widehat B=c(\theta)\). The scalar \(c\) is locally integrable in time by testing the identity against a fixed compactly supported spatial function of integral one. Using \(N_x=-KT\) gives
\[
 \partial_x(-GN+\alpha T)=B N,\qquad
 \partial_x(-GN+\alpha T-\widehat X_\theta)=cN .
\]
Since \(N=J\widehat X_x\), integration in space leaves a second locally integrable coefficient \(d(\theta)\in\mathbb R^2\). Now
\(\widehat X_\theta=-(a'/a)\widehat X+(a'x+\phi')T/a\). Taking the normal component yields
\[
              -G=(d+cJ\widehat X-(a'/a)\widehat X)\cdot N.             \tag{4}
\]
All products here are smooth in space except for the given locally integrable coefficients and the distributional derivative \(G_x\). The calculation holds for almost every time after taking spatial distributions. A different local lift of the phase changes the translation coefficient in (4) and leaves the scalar normal speed invariant.

Fix such a time, put \(P_K=P/a\), \(D=D_0/a\), \(M=cJ-(a'/a)\mathrm{Id}\). Formula (4) at \(x+nP_K\) has an extra term \(n(MD)\cdot N(x)\). If \(M\ne0\), then \(M\) is invertible. The normals of a nonstraight period span the plane, so the \(L^p\) norm of \((MD)\cdot N\) over a period is positive. The triangle inequality shows that on the \(n\)-th positive period the \(L^p\) norm of \(G\) is bounded below by a positive multiple of \(n\) for all sufficiently large \(n\). The liminf of \(R^{-(p+1)}\int_{-R}^R|G|^pdx\) is then strictly positive. Apply Fatou along the sequence from (2) and exhaust each open nonzero component by compact intervals. It follows that \(c=a'=0\) almost everywhere there. The amplitude is constant on each such component. At any finite endpoint inside \(I\), compactness of the phase circle would give a nonzero subsequential slice of that same amplitude, contrary to temporal continuity at a zero slice. Consequently a nonempty component fills \(I\).

The unweighted case of (3) follows from \(KN=T_x\). For a bounded measurable weight use \(T=(U',U^2/2)\), \(N=(-U^2/2,U')\) at \(y=ax+\phi\). In \(\int\omega(a|U|)U N\,dy\) the first component cancels under a half-period shift. The second integrates \(\omega(a|U|)U\,dU\) along a complete oscillation and vanishes by change of variable on its monotone arcs. This proves (3), including sharp cutoffs in the magnitude of curvature.

## Application to actual flows

On actual smoothly immersed curves the uncorrected stress \(S=(k^2/2)T+k_sN\) satisfies \(S_s=FN\). On fixed-dilation slabs with comparable lengths tending to infinity, bounded spatial mean of \(k^2\), bounded spacetime mean of \(F^2\), and positive curvature energy escaping to large amplitudes, a stopped material-tube construction produces a nonzero limit on a common positive time window and on the whole spatial line. Its weak speed satisfies (2) for \(1<p<2\), and its curvature and conservative flux satisfy (1). Therefore (3) applies. The sampling and compactness proof also passes \(K_jG_j\) against bounded tests on a fixed compact window, by removing exceptional times and pairing weak \(G_j\) with strongly convergent bounded truncated curvature. Taking the indicator of one limiting period in space and a bounded compactly supported time test shows that this one real rescaled period has vanishing limiting mixed flux. [Physical extraction from a set of positive curvature energy](PhysicalForcedRectangularTube.md)

The scale weight \(|S|\), which is independent of phase on the limiting oscillator, admits a genuine uniform spacetime mass bound under the same physical hypotheses. In fact on a closed smooth spatial slice put \(V=(1+|S|^2)^{1/2}\). Then \(|V_s|\le|F|,\ |k|\le\sqrt{2V},\ |k_s|\le V\). Integrate \((kk_s)'=k_s^2+kF-k^4/2\) against \(1/V\). The terms containing \(F\) or \(V_s\) have absolute integrals bounded by \(C\int |F|\,ds\). This gives
\[
 \langle V\rangle\le C(1+\langle k^2\rangle+\langle|F|\rangle)
\]
by \(V=(1+k^4/4+k_s^2)/V\). A localized version compares the tails. For \(B\ge1,\ 0<\delta<1\), take a smooth \(\zeta(V/B)\) equal to zero for \(V\le B\), one for \(V\ge2B\) and between zero and one. Use \(\zeta(V/B)/V\) in the same integration by parts. Its spatial derivative is at most \(C|F|{\bf1}_{V\ge B}/V^2\) in magnitude. Both force errors are therefore bounded by \(CB^{-1/2}\int |F|ds\). On the support of \(\zeta\), split \(k^4/V\) according to \(k^2\le\delta V\) or \(k^2>\delta V\). The resulting inequality is
\[
 \langle V{\bf1}_{V\ge2B}\rangle\le
 C\left[B^{-1}+\delta\langle k^2\rangle+
 \langle k^2{\bf1}_{k^2>\delta B}\rangle+B^{-1/2}\langle|F|\rangle\right].
\]
Consequently tightness of the spacetime curvature-energy tails is equivalent to tightness of the stress-weighted tails, since \(k^2\le2V\) gives the reverse implication. Substituting \(|S|\) for \(k^2\) as the initial sampling weight on the retained bands is legitimate: its total weight is bounded as above and it is between \(H^2\) and \(4H^2\) there. This change gives a weight that becomes constant on spatial periods in the limit. It does not control overlaps of the selected tubes, the relation between later flux and initial sampling measure, or growth on the region of bounded RMS curvature.

## A finite-window obstruction even with zero turning number

Take a smooth closed zero-turn immersion whose free elastic flow has \((EL)'(0)>0\), as constructed in the zero-turn appendix of the fixed-turning obstruction. By smoothness, it has strictly positive \((EL)'\) throughout some fixed nonzero initial interval. Its \(n\)-fold cover is a true free elastic flow on that interval. Covering multiplies each of \(L,E,D=\int F^2ds\) by \(n\), and multiplies \(EL\) and \((EL)'\) by \(n^2\). Thus its initial \(EL\) becomes arbitrarily large while the RMS factor \(m^2=2E/L\), the dimensionless growth \(L(EL)'/E^3\), its sign on that time window, and the zero turning number are preserved. [Fixed turning, including zero](../../FixedTurningObstruction.txt)

One can also require the initial immersion to be parametrized on its minimal arclength period. To break the cover, pick a fixed unit vector \(e\), a parameter \(q_0\) maximizing \(e\cdot X\), and a smooth bump \(\psi\) with a unique strict global maximum of one at \(q_0\). Replace the initial map by \(X+\nu\psi e\) with sufficiently small \(\nu>0\). Its height in direction \(e\) now attains its maximum at exactly one parameter, excluding every nontrivial cover. It remains immersed with the same turning number. For each fixed \(n\), ordinary continuous dependence of the smooth free elastic flow on the smooth initial immersion preserves strict growth on a slightly shorter fixed window when \(\nu=\nu_n\) is sufficiently small. In detail, in a strictly parabolic tangential gauge the derivative of the initial-data and evolution map is a uniformly parabolic fourth-order initial-value operator with invertible Hölder solution map on the given smooth compact interval. The implicit function theorem gives continuity in \(C^{4+\alpha,1+\alpha/4}\); on this neighborhood \(L,E,D,(EL)'\) are continuous uniformly in time. One may choose the shorter physical interval independent of \(n\) by starting with a strict lower bound on the base interval, and may then shorten once more to a common fixed RMS duration by choosing the perturbed \(m\) arbitrarily close to that of the base. This construction concerns different initial data on a fixed interval. The growth of \(EL\) along one evolving immersion over arbitrarily late times remains undetermined. [Parabolic gauge and invertible linear initial-value problem, Section 3](https://arpi.unipi.it/retrieve/21ccf6e4-9e07-4e70-ab78-8b1c5137f17a/s00032-021-00327-w.pdf)

The modulation, sampling, and finite-window statements above are written proofs. They have no Lean verification.

