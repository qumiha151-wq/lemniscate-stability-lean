# Macroscopic tangent-angle oscillations at increasing energy-length records

For a regular oriented closed curve let \(m\) be the largest number of subarcs with pairwise disjoint interiors on each of which the absolute net change of a continuous tangent-angle lift is at least \(\delta=1/4\) radian. Either sign is allowed independently on each arc. The arc can contain arbitrarily many curvature zeroes. This finite integer is unchanged by rigid motions, dilation, choice of parameter origin, or regular reparametrization. Its finiteness follows from \(m\delta\le \int |k|\,ds\).

**Theorem.** Normalize a smooth closed immersed curve to unit root-mean-square curvature, let \(P\) be its length, put \(f=k_{ss}+k^3/2\), and write \(d=P^{-1}\int f^2\,ds\). Then
\[
                       d\le1/4 \quad\Longrightarrow\quad
                       P^4\le 2^{23}m^6d .
\]
On a genuine forward normal free elastic flow write \(E=\tfrac12\int k^2ds\), \(L\) for length, \(U=EL\). If the sharp upper bound \(L(t)=O((1+t)^{1/4})\) fails, there exist arbitrarily late slices with \(U\) arbitrarily large on which
\[
                        m\ge 2^{-19/6} U^{1/3}.
\]
In particular, an eventual bound \(m=o(U^{1/3})\) along high-product slices gives the sharp upper bound. Equicontinuity of the unit tangents on the parameter circle after a choice of regular reparametrizations on the late slices is sufficient.

**Proof.** Use RMS coordinates and put \(M=\max|k|\), \(J=\int |f|\,ds\). Cauchy–Schwarz gives \(J\le P/2\). For a connected component \(I\) of the nonzero-curvature set having endpoints, write \(M_I=\sup_I|k|\), \(\theta_I=\int_I |k|\,ds\), \(Y_I=\int_I k_s^2\,ds\), and \(J_I=\int_I |f|\,ds\). Both endpoint values of \(k\) vanish. Integrating the derivative of \(|k|^{3/2}\) from one endpoint to a maximum and using Cauchy–Schwarz gives
\[
 M_I^3\le(9/4)\theta_I Y_I,\qquad
 \int_I k^4\le M_I^3\theta_I\le (9/4)\theta_I^2Y_I.
\]
Integration by parts yields \(M_I J_I\ge Y_I-\tfrac12\int_I k^4\). For a small lobe with \(\theta_I\le1/4\), we obtain
\[
 \int_I |k|^3\le M_I^2\theta_I
       \le \frac{9}{4(1-9\theta_I^2/8)}\theta_I^2 J_I
       \le 3\delta^2 J_I .
\]
Sum over all small lobes using countable additivity and apply Hölder on their union \(S\). This gives
\[
 \int_S k^2\le |S|^{1/3}\left(\int_S |k|^3\right)^{2/3}
       \le P(3/32)^{2/3}<P/2.
\]
If \(k\) never vanishes, the entire circle has one sign and total absolute turning at least \(2\pi\) by Fenchel, so all the curvature energy belongs to a single large lobe. Otherwise cut at a zero. Each large lobe contributes \(\lfloor\theta_I/\delta\rfloor\ge\theta_I/(2\delta)\) disjoint arcs of absolute signed turning exactly \(\delta\), by moving successively along that lobe. The same subdivision works on the single-sign circle after any cut. Thus the combined turning of the large lobes is at most \(2\delta m\). The zero set carries no curvature-squared mass. It follows that \(P/2\le 2\delta mM\), or \(P\le mM\). The closed-curve pointwise stress estimate gives
\[
 M^6\le 2^{24}E\int f^2\,ds = 2^{23} P^2d.
\]
Combining the inequalities proves the first claim.

Now return to unscaled variables, so \(P^2=2U\) and \(d=\mathcal D L^2/(8E^3)\), where \(\mathcal D=-E'\). Because \(L'\le \sqrt{2E\mathcal D}\), a time with \(U'=E L'-L\mathcal D\ge0\) has \(d\le1/4\); strict positivity of \(\mathcal D\) follows from the closed-curve virial. Hence \(m^6\ge2^{-21}P^4=2^{-19}U^2\) there.

The previously established length-growth equivalence states that the sharp upper bound holds if and only if \(U\) is bounded over the trajectory. If \(U\) is unbounded, take the first times of increase to any sequence of levels tending to infinity above the initial value. Continuity provides each first time, differentiability there gives \(U'\ge0\) from the left, and compact-time boundedness makes the times tend to infinity. This proves the trajectory assertion.

On each counted arc one can shorten the arc until the net angular change is exactly \(\delta\) in absolute value. The unit tangents at its endpoints differ by \(2\sin(\delta/2)\). An equicontinuous family on a fixed unit parameter circle has a common positive lower bound on the parameter lengths of such arcs. It consequently has uniformly bounded \(m\). In particular, along the increasing records of a flow violating the quarter bound, no subsequence of unit tangent maps converges uniformly under any choices of regular reparametrizations. Uniform convergence of a subsequence would give equicontinuity for that subsequence, contradicting \(m\to\infty\).

This is an analytic proof. The small-lobe summation and tangent-angle excursion count in this note have not been checked in Lean. The material length-growth equivalence and the pointwise stress estimate used here are separately verified in the LengthGrowth project.
