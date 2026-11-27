# Directional turning on a finite remaining length clock

Write \(E=\frac12\int k^2ds,\ L=\int ds,\ U=EL,\ F=k_{ss}+k^3/2\) on a smooth closed planar free elastic flow with velocity \(-FN\) in a material parametrization. Write \(\mathcal A=\int |k|ds\), \(\tau(t)=\int_0^t L^{-4}dr\), and suppose \(\delta(t)=\tau(\infty)-\tau(t)<\infty\). Put \(\Omega(t)=U(t)\sqrt{\delta(t)}\). The finite-clock comparison gives \(U^{-2}\le\delta\), hence \(U(t)\to\infty\). [Finite-clock identity](FiniteClockGrowthCorrection.md)

## Angular cost at the finite-clock rate

If \(\mathcal A(t)/\sqrt{2U(t)}\to0\), then \(\Omega(t)\to\infty\). To prove this, start at time \(t_0\) and put \(m_0^2=2E_0/L_0\). In the initial RMS units the period is \(P=\sqrt{2U_0}\), the starting energy is \(P/2\), and the physical secant inequality \(\int (L')^2dt\le E_0^2\) gives \(P/2\le L\le3P/2\) throughout the first unit window. Thus \(U\le3U_0/2\) in that window. The hypothesis implies that the mean of \(\mathcal A/P\) tends to zero uniformly for late starting times. The angular cost for a fixed relative length change therefore gives \(\sup|L/L_0-1|\to0\) throughout the window. [Angular cost on actual unit RMS windows](HighStressSignedFlux.md)

Restart the window \(N\) times for any fixed integer \(N\). On their union the length is \((1+o(1))L_0\). Monotonicity of \(E\) implies that each restarted window has physical duration at least \((1-o(1))m_0^{-4}\). Consequently
\[
       \delta(t_0)U_0^2\ge (1-o(1))\,N\,U_0^2m_0^{-4}L_0^{-4}
                         =(1-o(1))N/4 .
\]
Taking \(t_0\to\infty\) and then \(N\to\infty\) proves the claim.

A bounded value of \(\Omega\) forces repeated turning through an entire interval of directions. Fix \(M\ge1\). There exist positive constants \(c,r,b_-,b_+\), a finite list of proper open arcs \(J_\nu\) of the unit circle of a common positive angular width, and a threshold, depending only on \(M\), with this property. Start at \(U_0\) above the threshold with \(\Omega(t_0)\le M\), in the initial RMS units used above. Within the next \(65 M^2\) time units there are a set of times of measure at least \(c\), one \(J_\nu\) and one sign, independent of time on this set, such that at each such time:

* There are at least \(cP\) pairwise interior-disjoint arclength intervals of length \(2r\). On each, the curvature has the specified sign and \(b_-\le |k|\le b_+\). Its tangent turns monotonically through all of \(J_\nu\).
* If \(d\) is the turning number, at least \(cP-|d|\) complete passages through the same arc occur in the opposite direction. Each of these passages has net turning equal in magnitude to the arc width. Its curvature need not have a constant sign.

All lengths, times and curvatures in these two assertions use the fixed initial normalization. The chosen sector and sign can depend on the starting slice. For a sequence one can fix them on a subsequence. No bound on \(d\) is needed for the first assertion. The second gives a growing count for each fixed \(d\).

### A proportional length change produces many arcs of definite curvature

In initial RMS units \(U_0=P^2/2\). The interval on which \(P/2<L<2P\) must end at some \(v\le 65M^2\). Otherwise its length-clock cost is at least \(65 M^2/(16P^4)> M^2/U_0^2\). Up to this first exit \(E\le P/2,\ \langle k^2\rangle\le2,\ \int\langle F^2\rangle dt\le1\), and \(|L(v)-P|\ge P/2\). Also \(v\ge1\) by the secant estimate. Here \(\langle\cdot\rangle\) is the arclength average.

Use the spacetime measure \(d\mu=ds\,dt/P\) on \([0,v]\). There is a fixed \(B=B_M\) such that the part of the signed flux with \(|S|\le4B^2\), \(S=(k^2/2)T+k_sN\), carries a fixed amount after taking its sign, in the following precise sense. Put \(\sigma=\operatorname{sgn}(L(v)-P)\), and take the smooth high-stress cutoff \(\zeta\) of the signed-flux theorem. Then
\[
             \int (1-\zeta(|S|/B^2))\,\sigma kF\,d\mu\ge1/4 .         \tag{1}
\]
Otherwise choose \(B_j\to\infty\) and violating high-product windows. Extract \(v_j\to v_*\in[1,65M^2]\), work on fixed compact subintervals of \((0,v_*)\), and discard endpoint strips of width \(\epsilon\) at cost \(O_M(\sqrt{\epsilon})\) by Cauchy–Schwarz, uniformly for either cutoff. The total high-stress signed flux then tends to zero by the high-stress theorem. This contradicts the length change. The same argument gives uniform constants for any fixed-length slab with the two mean budgets, comparable periods and a definite relative length change. [Vanishing high-stress signed flux](HighStressSignedFlux.md)

On the support of the low-stress factor in (1), \(|k|\le\sqrt8 B\). The absolute contribution with \(|k|<a\) is \(O_M(a)\) by Cauchy–Schwarz. The part with \(|F|>D\) costs \(O_M(B/D)\) using the squared force budget. Choose \(a>0\) small, then \(D\) large. Removing samples with \(\sigma kF\le0\) can only increase the remaining integral. Since its integrand is bounded above by \(\sqrt8 BD\), a set of \(\mu\)-measure bounded below remains on which \(|k|\ge a,\ |S|\le4B^2,\ |F|\le D\). A further subset of uniformly positive measure satisfies \(\int_{s-1}^{s+1}F^2dy\le Q_M\): the integral of this local quantity in \(d\mu\) is bounded by twice the spacetime \(F^2\) budget, by spatial Fubini. The unit-radius intervals do not wrap once \(P\) is sufficiently large.

Since \(S_s=FN\), every point of the unit neighborhood of such a center has \(|S|\le 4B^2+\sqrt{2Q_M}\). There \(|k_s|\le |S|\) and \(k^2\le2|S|\). Choose \(0<r<1/4\) so on the radius-\(r\) interval \(|k|\) stays at least \(a/2\) with the same sign and the full angular change is less than \(\pi/2\). Its angle advances by at least \(ar/2\) on each side of the center.

Choose finitely many direction bins of diameter less than \(ar/8\), each contained in a direction sector of width \(ar/4\) around its center. Each radius-\(r\) interval belonging to a center in the bin passes monotonically through that whole sector. One bin and one sign contain a positive \(\mu\)-measure of good centers. Because \(L\le2P\) and \(v\le65M^2\), there is a time set of uniformly positive measure on which their arclength is at least \(c_1P\). On such a slice take a maximal collection of disjoint radius-\(r\) intervals with these centers. The concentric radius-\(2r\) intervals cover the center set, giving at least \(c_1P/(4r)\) chosen arcs.

### Counting complete passages through a fixed direction sector

For a proper open direction arc \(J\) with a chosen positive angle coordinate, call a component of \(T^{-1}(J)\) a positive complete passage if its entry and exit are the lower and upper endpoints of \(J\), and a negative one for the reverse order. Components that return to the same endpoint have signed contribution zero. Denote the respective complete counts by \(n_+,n_-\). For every smooth unit tangent map on the oriented parameter circle,
\[
                             n_+-n_-=\deg(T)=d .                       \tag{2}
\]
To verify it, take a nonnegative smooth function \(\chi\) supported in \(J\) whose integral in the angle coordinate over \(J\) is one. The integral of \(\chi(T)k\,ds\) around the parameter circle equals \(d\) by lifting the tangent angle through one full traversal. On each component of \(T^{-1}(J)\), integration of an antiderivative along the lifted path gives \(+1,-1\) or zero according to its endpoints. The sum over components is absolutely integrable, bounded in absolute variation by \(\|\chi\|_\infty\int|k|ds\). The complete counts are therefore finite. If \(T^{-1}(J)\) is the whole circle, its image has a real lift inside \(J\) and both sides of (2) are zero. This proof permits infinitely many incomplete excursions and tangencies to the endpoints. For almost every direction in \(J\), Sard's theorem additionally makes all its preimages regular. Each complete passage then contains an appropriately signed transverse preimage. Each monotone crossing in the first assertion belongs to a different complete component, so (2) gives the second assertion.

## The physical rate of growth of directional crossings

The same test defines \(\mathcal A_\chi(t)=\int\chi(T)|k|ds\). On smooth compact time intervals it is Lipschitz and satisfies the exact formula
\[
 \mathcal A_\chi'(t)=
 -\sum_{I=(a,b)\ {\rm component\ of}\ \{k\ne0\}}
 \operatorname{sgn}(k|_I)\,[\,\chi(T)F_s\,]_{a}^{b}
 =:\Gamma_\chi(t)                                                       \tag{3}
\]
for almost every time. If the curvature has no zeros the full-period endpoint term is zero. Indeed at fixed material labels \(\theta_t=-F_s\), and \((k\,ds)_t=-F_{ss}ds\). The absolute-value chain rule holds at almost every material time and gives zero derivative at zeros for almost every spacetime point. Differentiating \(\mathcal A_\chi\) and grouping terms on each nonzero-curvature component gives the integral of \(-\operatorname{sgn}k\,(\chi(T)F_s)_s\). The sum of the absolute endpoint differences is bounded by \(\int|(\chi(T)F_s)_s|ds\) on each smooth slice. [Material turning and the one-sided inflection estimate](../OneSidedTurning/OneSidedTurning.md)

In fact the series can be regrouped by individual zeros, even for a smooth curve with infinitely many inflections. For any nonempty finite selection of distinct zeros \(z_1,\dots,z_n\), list them in positive cyclic order, extending the list periodically on the parameter cover. The four distinct lifted zeros from \(z_i\) to \(z_{i+3}\) give by three applications of Rolle a zero of \(k_{sss}\) in that interval. Hence
\[
 \sum_i|F_s(z_i)|=\sum_i|k_{sss}(z_i)|
       \le \sum_i\int_{z_i}^{z_{i+3}}|k_{ssss}|ds
       =3\int|k_{ssss}|ds .
\]
The same count works for \(n<4\) because the list is extended on the cover. Taking the supremum over finite selections bounds the sum over all zeros. At a nonisolated zero, Rolle applied to a sequence of neighboring zeros gives \(k_{sss}=0\), hence \(F_s=0\). An isolated zero with the same sign on both sides contributes cancelling endpoints. If \(Z_{\rm ch}\) is the set of isolated sign-changing zeros and \(\varepsilon_z=+1\) for a change from negative to positive curvature and \(-1\) for the reverse change, then
\[
        \Gamma_\chi=2\sum_{z\in Z_{\rm ch}}\varepsilon_z\chi(T(z))F_s(z),
 \qquad |\Gamma_\chi|\le6\|\chi\|_\infty\int|k_{ssss}|ds .
\]
At a simple zero \(\varepsilon_z=\operatorname{sgn}k_s(z)\). At a degenerate isolated sign change the formula uses the change of sign itself. Thus the exact directional rate measures the net contribution of inflections with tangent in the support of the prescribed angle test. This argument imposes no finiteness or simplicity condition on the zero set.

For each of the finitely many sectors fix one such \(\chi\). At a time selected above, \(\mathcal A_\chi\ge n_++n_-\ge 2cP-|d|\). Hence on a single finite-clock trajectory with bounded \(\Omega(t_j)\) at arbitrarily late times, a subsequence has the same \(\chi\) and there are later times \(r_j\) in the stated windows for which, for every fixed earlier \(t_*\),
\[
                    \int_{t_*}^{r_j}\Gamma_\chi(t)\,dt
                       \ge 2c\sqrt{2U(t_j)}-|d|-\mathcal A_\chi(t_*).
\]
This follows from the actual normal velocity in material coordinates and requires no tracking of inflection labels from one time to another. The physical energy budget controls \(\int F^2ds\,dt\). A bound strong enough on this directional inflection rate along an arbitrary single orbit is still missing. These results are written proofs, without Lean verification.

