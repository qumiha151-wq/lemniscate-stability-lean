# Winding area and the cost of successive records on one elastic flow

For a closed oriented planar immersion \(X\) let \(n_X(z)\) be its winding number about a point off its image and set \(W(X)=\int_{\mathbb R^2}|n_X(z)|\,dz\). Both leaves of an oppositely oriented figure eight contribute positively. The quantity is unchanged by rigid motions and reversal of the parameter, and scales as squared length.

Consider a single smooth closed normal free elastic flow with length \(L\), energy \(E=\tfrac12\int k^2ds\), force \(F=k_{ss}+k^3/2\), dissipation \(D=\int F^2ds\) and product \(U=EL\). For a global record time \(t\), meaning \(U(v)\le U(t)\) for all \(0\le v\le t\), and \(0\le s\le t\), one has
\[
 \frac{\|n_{X(t)}-n_{X(s)}\|_{L^1(\mathbb R^2)}}{L(t)^2}
 \ \le\ \frac{\log(E(s)/E(t))}{2\pi}.                                      \tag{1}
\]
The winding numbers in the difference refer to the original physical plane. In particular
\[
 \frac{W(X(t))}{L(t)^2}\le
 \frac{L(s)^2}{4\pi L(t)^2}+\frac{\log(E(s)/E(t))}{2\pi}.                  \tag{2}
\]
If \(U(t)\ge q U(s)\) for \(q>1\) and \(W(X(t))\ge aL(t)^2\), then
\[
                 \log\frac{E(s)}{E(t)}\ \ge\ 2\pi a-\frac1{2q^2}.          \tag{3}
\]
Thus repeated well-separated records at which the normalized winding area stays above \(a>0\) force geometric decay of the actual bending energy with the number of these records.

If \(E_\infty=\lim_{t\to\infty}E(t)>0\), every sequence of unbounded product records satisfies \(W(X(t_j))/L(t_j)^2\to0\). More generally the same conclusion holds on unbounded length records, or times at which the running maximum length is at most a fixed multiple of the current length. This excludes a normalized limiting profile with nonzero winding area on such a trajectory.

## The swept-area bound

Write \(S=\int |F|ds\). A smooth homotopy \(H\) from \(X_0\) to \(X_1\) satisfies
\[
 \|n_{X_1}-n_{X_0}\|_1\le\iint |\det(H_v,H_u)|\,du\,dv .
\]
Indeed for a regular value away from the endpoint loops the winding difference is the signed number of preimages in the cylinder. Taking absolute values and applying the area formula gives the bound. The endpoint images and critical values have planar measure zero. The same inequality for a linear homotopy of Lipschitz loops follows by smooth approximation or the Lipschitz area formula. In particular, two loops with the same parameter domain, lengths \(L_X,L_Y\), and maximum pointwise separation \(d\) satisfy
\[
                   |W(X)-W(Y)|\le d(L_X+L_Y)/2.                           \tag{4}
\]
Here the homotopy derivative in its interpolation variable has size at most \(d\) and its length at interpolation fraction \(v\) is at most \((1-v)L_X+vL_Y\).

For the cone from the arclength centroid \(z\) to \(X\), the same bound using the actual Jacobian is \(W(X)\le\frac12\int|X-z|ds\). Cauchy–Schwarz and periodic Wirtinger give \(W(X)\le L^2/(4\pi)\) for all closed immersions with arbitrary multiplicity. A stronger classical estimate bounds the integral of the square of the integer winding number by the same expression. [Banchoff–Pohl inequality for self-intersecting curves](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/isoperimetric-inequality-for-curves-with-selfintersections/136044B69F8EEFD0793013840A52F3E1)

For the physical flow \(X_t=-FN\) the unsigned Jacobian integral per unit time is exactly \(S\). Cauchy–Schwarz gives \(S^2\le LD\). The dilation identity \(\left|\int F(X-z)\cdot N\,ds\right|=E\), Cauchy–Schwarz and periodic Wirtinger imply \(4\pi^2E^2\le DL^3\). Multiplying these inequalities gives
\[
            2\pi S/L^2\le D/E=-(\log E)'.
\]
The coefficient is attained by a once-traversed expanding circle. On any interval with \(L\le R\) this gives \(2\pi\int_s^t S\le R^2\log(E(s)/E(t))\). At a product record, \(E(v)\ge E(t)\) implies \(L(v)\le L(t)\) for \(v\le t\). This proves (1). The cone estimate gives (2), and monotonicity of \(E\) gives \(L(s)/L(t)\le U(s)/U(t)\), proving (3). For a positive energy limit, fix \(s\), send \(j\to\infty\) in (2), and then \(s\to\infty\). A bounded ratio of running to current length multiplies the logarithmic term by at most the square of that ratio.

## Minimum time for an individual passage, including when the energy tends to zero

Suppose \(t\) is a product record, \(W(X(t))\ge aL(t)^2\), and \(s<t\) is an earlier time with \(L(s)=L(t)/q\), where \(q>1\) and \(d=a-1/(4\pi q^2)>0\). Such an \(s\) exists after every sufficiently large length increase. If the preceding product record was at most \(U(t)/q\), one can choose \(s\) between the two records. For the terminal RMS curvature scale \(m_t=(2E(t)/L(t))^{1/2}\) and length clock \(d\tau=L^{-4}\,dt\), the bounds are
\[
 m_t^4(t-s)\ge\frac{4d^2U(t)}{q-1},\qquad
 \tau(t)-\tau(s)\ge\frac{d^2}{(q-1)U(t)}.                                  \tag{4a}
\]
Indeed \(\int_s^tS\,dv\ge W(t)-W(s)\ge dL(t)^2\). Cauchy–Schwarz in time gives
\[
 d^2L(t)^4\le\left(\int_s^tS\,dv\right)^2
 \le L(t)(t-s)\big(E(s)-E(t)\big).
\]
The product record gives \(E(s)L(t)/q\le E(t)L(t)\), and throughout the interval \(L\le L(t)\). These observations prove both estimates. In particular the RMS duration must diverge at least linearly in the terminal product even when \(E_\infty=0\).

If \(\tau_*=\tau(\infty)<\infty\), and every sufficiently high product record has \(W/L^2\ge a\), write \(U^*(v)=\max_{r\le v}U(r)\). Finite clock entails unbounded product. After any late \(v\), let \(t\) first hit \(qU^*(v)\); then \(L(v)\le L(t)/q\). Taking \(s\ge v\) in (4a) proves \(U^*(v)(\tau_*-\tau(v))\ge d^2/[q(q-1)]\). This improves the power of the usual square-root necessary growth law under the stated geometric hypothesis. [General finite-clock result](../SaturationGeometry/FiniteClockGrowthCorrection.md)

## A growth exponent from length records

Suppose \(W(X(t))\ge a L(t)^2\) whenever \(L(t)=\max_{0\le v\le t} L(v)\) is sufficiently large, for a fixed \(0<a\le1/(4\pi)\). Then
\[
                  L(t)=O\big((1+t)^{1/(3+4\pi a)}\big).                  \tag{5}
\]
No monotonicity of \(L\) between records is assumed. Put \(R(t)=\max_{0\le v\le t}L(v)\). The running maximum is locally absolutely continuous, and \(dR\) is supported on \(\{L=R\}\). The swept-area inequality gives local absolute continuity of \(W(t)\) and \(|W'|\le S\) almost everywhere. Starting at a record \(s\) past the assumed threshold, integration by parts yields
\[
 \log(E(s)/E(t))\ge 2\pi\int_s^t W'(v)/R(v)^2\,dv
 =2\pi[W/R^2]_s^t+4\pi\int_s^t(W/R^2)\,d\log R
 \ge -\tfrac12+4\pi a\log(R(t)/R(s)).
\]
Consequently \(E(t)\le C R(t)^{-4\pi a}\). If \(R\) is bounded, (5) is immediate. Otherwise fix \(q>1\) so that \(q^{-2}/(4\pi)\le a/2\). Let \(t_1,t_2\) be first hits of \(R_*/q,R_*\), with the lower level beyond the threshold. Then \(W(t_2)-W(t_1)\ge a R_*^2/2\). By the unweighted swept-area bound and Cauchy–Schwarz in time,
\[
 a^2R_*^4/4\le\left(\int_{t_1}^{t_2}\sqrt{LD}\,dt\right)^2
 \le R_*(t_2-t_1)E(t_1)\le C R_*^{1-4\pi a}t_2.
\]
Taking first hits and using the running maximum proves (5).

## The high-level trigonometric outward profiles

Fix the turning number \(m\) and use the explicit analytic curves at prescribed levels from [PrescribedTrigonometricLevels.md](../MulticoverBarrier/PrescribedTrigonometricLevels.md). As the level increases, \(N\to\infty,\ c=A/N\to1\), and \(\langle e^{ic\phi}\rangle\to M\ge1/5\). After passing to a subsequence in the zero-turn slow coefficient \(a\in[0,3]\), the positions, with length \(2\pi\), converge uniformly to
\[
       Y(s)=M\int_0^s e^{i(mv+a\sin v)}\,dv,\qquad 0\le s\le2\pi .
\]
To verify uniformity, subtract from the fast factor its period average. Its primitive has uniform size \(O(N^{-1})\). Integration by parts against the slow factor, whose first derivative is bounded by \(|m|+3\), gives a uniform \(O_m(N^{-1})\) error on every partial interval.

When \(m\ne0\) the construction uses \(a=0\). The limit is a circle of radius \(M/|m|\) with \(|m|\) traversals, giving \(W(X)/(2\pi)^2\to M^2/(4\pi|m|)>0\). When \(m=0\), exact closure gives \(\int_0^{2\pi}\cos(a\sin s)\,ds=0\). Its integrand is positive almost everywhere for \(0\le a\le\pi/2\), so \(\pi/2<a\le3<\pi\). The height of \(Y\) increases strictly on \((0,\pi)\) and decreases strictly on \((\pi,2\pi)\). The two branches at each height have opposite horizontal coordinates, since \(Y(2\pi-s)=(-Y_1(s),Y_2(s))\). Near \(s=0\) the first branch has strictly positive horizontal coordinate. Every sufficiently low positive height therefore cuts the bounded region between these two branches at points of winding magnitude one, by transverse ray intersection. Thus \(W(Y)>0\). Compactness of the possible \(a\) and (4) give a uniform positive lower bound for the actual large-level zero-turn profiles as well.

This bound persists under a normalized positional error tending to zero, allowing translations, rotations, reflections and reparametrizations. Thus a single unbounded record sequence that approaches these explicit representatives must have \(E_\infty=0\). It must also obey the quantitative energy loss (3) on every sufficiently separated subsequence of such records. A general flow might have vanishing limiting energy or approach profiles with vanishing normalized winding area. These possibilities leave the unrestricted length-growth question open.

The independent Lean modules check the actual material integral \(S\), the sharp logarithmic cost through each product record, the vanishing of total swept area in units of squared record length when \(E_\infty>0\), and the terminal RMS lower bound from a prescribed amount of actual swept area. The planar winding homotopy argument, its geometric consequences and the profile limits are proved above.
