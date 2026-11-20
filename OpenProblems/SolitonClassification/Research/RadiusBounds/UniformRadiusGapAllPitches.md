# A circumradius gap for closed similarity expanders at every pitch

Normalize the dilation coefficient to one and place the similarity centre at the origin. Let \(R=\max_s|X(s)|\), where \(X\) is a smooth closed unit-speed planar immersion and
\[
  F=k_{ss}+\tfrac12 k^3=-p-bq,\quad
  p=X\cdot N,\quad q=X\cdot T,\quad p'=-kq,\quad q'=1+kp .
\]
The number \(b\) is any real rotation coefficient. There is an absolute \(\delta>0\) such that each noncircular closed similarity expander has
\[
                         R\ge 2^{-1/4}+\delta .
\]
All windings, covering numbers, geometric periods and pitches are included. The numerical size of the gap is not computed. The proof below is analytic.

## The radius potential and a local stress bound

Set \(v=k'\), \(W=(k^2/2)T+vN\), and \(H=qv-pk^2/2-k\). Direct differentiation gives \(W'=FN,\ H'=Fq\). Consequently, with \(c=1/R^2\), \(J=X\cdot W-bH+cq\),
\[
 \begin{split}
 J'&=\tfrac12(k+cp)^2+c-(1+c^2/2)p^2+b^2q^2=\mathcal A-\varepsilon,\\
 \mathcal A&=\tfrac12(k+cp)^2+(1+c^2/2)(R^2-p^2)+b^2q^2,\qquad
 \varepsilon=R^2-\tfrac1{2R^2}.
 \end{split}
\]
The full geometric period returns all factors. Its mean of \(\mathcal A\) is \(\varepsilon\), so \(R\ge R_*:=2^{-1/4}\); equality gives a circle from \(p^2=R^2\), \(q=0\) and \(kp=-1\). Write \(k_*:=1/R_*\).

Here is a pointwise estimate valid independently of the period. Assume \(|X|\le R\) and \(|F|\le B\) on the periodic extension, with \(B>0\). At an arbitrary point put \(w=|W|\). For \(w>0\) take the following interval of length \(T_0=w/(4B)\). Throughout, \(3w/4\le |W|\le5w/4\), \(|v|\le5w/4,\ k^2\le 5w/2\). Integrating \((X\cdot W)'=k^2/2+Fp\) gives an interval mean \(\overline{k^2}\le C R B\), since the endpoint difference is at most \(C Rw\). Also
\[
                  (kv)'=|W|^2-\tfrac34 k^4+kF .
\]
The boundary term after averaging is at most \(Cw^{3/2}/T_0\), and \(\overline{k^4}\le(5w/2)\overline{k^2}\). Thus \(w^2\le C(B\sqrt w+RBw)\), whence
\[
                  \|W\|_\infty\le C(B^{2/3}+RB).
\]
This argument can use an interval spanning many full periods. We shall use \(B=(1+|b|)R\).

Suppose for contradiction that noncircular profiles have \(R_n\to R_*\). A reflection sends \(b\) to \(-b\), so we may use nonnegative pitches.

## Bounded rotation coefficients

When \(b_n\to b_0<\infty\), the pointwise bound controls all four support coordinates, and their polynomial ODE controls all derivatives locally on the extended arclength line. After any independently chosen arclength shifts, a subsequence converges on compact intervals to a complete solution with \(|X|\le R_*\) in support coordinates. Its function \(J\), computed with \(c_*=1/R_*^2\), is nondecreasing.

If \(J'=0\) at a limiting point, \(\mathcal A=0\) gives \(p^2=R_*^2,\ q=0,\ kp=-1\). For \(r^2=p^2+q^2=|X|^2\), one has \((r^2)'=2q\), \((r^2)''=2(1+kp)\), and \((r^2)'''=2(vp-k^2q)\). At this maximum the first two derivatives vanish, so the third vanishes as well. Hence \(v=0\) and the limiting state is a circle equilibrium. The only two corresponding values of \(J\) are \(\pm b_0 k_*/2\).

On a periodic profile \(J'_n=0\) at each maximum. Thus some value of \(J_n\) tends, along a subsequence, to one of the two circle values. Its entire range is uniformly bounded. If these ranges failed to shrink to this one value, an interval of fixed positive width avoiding both circle values would be contained in infinitely many ranges. Periodicity supplies a downward crossing of that interval, and somewhere on it \(J'_n\le0\). Passing to the complete shifted limit gives \(J'=0\) there and so a circle value inside the disjoint interval, a contradiction. Hence \(\operatorname{osc}J_n\to0\). On any shifted limit \(J\) is constant. All the limit states must then be equilibria. Each noncircular closed profile has a curvature zero, by one-sign rigidity for actual similarity solutions. Shifting to such a zero contradicts the conclusion.

## Unbounded rotation coefficients

Suppose \(b=b_n\to+\infty\); all small-o estimates below are uniform over the chosen periodic trajectory. Put \(K=J/b\). Then \(K'=(\mathcal A-\varepsilon)/b\). The local stress estimate gives
\[
                 |v|\le Cb,\qquad |k|\le C\sqrt b .
\]
Two mean bounds will be used on intervals. Whenever \(\overline{\mathcal A}\le\varepsilon\), the mean of \(k^2\) is bounded since \(k=(k+cp)-cp\). On either a full period or an interval of length at least \(b\), this implies
\[
                            \overline{v^2}\le Cb .
\]
Indeed integrate \(v^2=(kv)'+k^4/2-kF\). The \(k^4\) mean is at most \(Cb\overline{k^2}\), and \(|F|\le Cb\) bounds the last term by \(Cb\,\overline{|k|}\). The boundary contribution vanishes for a period and is at most \(Cb^{3/2}/b\) otherwise.

The full-period mean of \(\mathcal A+(v/b)^2\) tends to zero. Thus there are good points where \(p\to\pm R_*, k+cp\to0,\ bq\to0,\ v/b\to0\). At any such sequence of points,
\[
 K=(qk^2/2+pv+cq)/b-qv+pk^2/2+k\ \longrightarrow\ \pm k_*/2 ,
\]
using \(kp\to-1\) and \(qv=(bq)(v/b)\). The same good-point assertion holds on every interval of length at least \(b\) with \(\overline{\mathcal A}\le\varepsilon\).

We claim \(\operatorname{osc}K\to0\). If the claim fails, pass to a subsequence so a full-period good value tends to one fixed circle value and the ranges have width bounded below. Then an interval \([A_0,B_0]\) of fixed positive width separated from both circle values is contained in every range on a further subsequence. This uses only connectedness of the ranges and does not require a pre-existing upper bound for \(K\). By periodicity select a complete downward crossing with \(K\) staying in this interval. Since \(K'\ge-\varepsilon/b\), its length is at least \(b(B_0-A_0)/\varepsilon\), which exceeds \(b\) eventually. The integrated derivative identity gives \(\overline{\mathcal A}\le\varepsilon\) on the crossing. The good-point conclusion supplies values approaching a circle value inside the separated interval, giving a contradiction.

On every following window \(I_s=[s,s+b]\), the derivative identity now gives
\[
 \int_{I_s}\mathcal A\le b(\varepsilon+\operatorname{osc}K)=o(b),\qquad
 \int_{I_s}q^2=o(1/b).
\]
Since \(|q'|=|1+kp|\le C\sqrt b\), a value \(|q(s)|=A\) forces \(|q|\ge A/2\) on the next interval of length \(A/(2C\sqrt b)\). That interval lies in \(I_s\). The square-integral bound gives \(A^3=o(b^{-1/2})\), so \(q\to0\) uniformly. Also
\[
 \operatorname{osc}_{I_s} r^2\le 2\sqrt b\left(\int_{I_s}q^2\right)^{1/2}=o(1).
\]
The mean of \(R^2-p^2\) on this same window tends to zero. Therefore \(r^2\to R_*^2\) uniformly, and \(p^2=r^2-q^2\to R_*^2\) uniformly. By connectedness and a subsequence there is a fixed \(p_0=\pm R_*\) such that \(p\to p_0\) uniformly.

Next, \(M:=\max|k|=o(b^{1/3})\). Otherwise take a subsequence \(M\ge\eta b^{1/3}\) for a fixed \(\eta>0\), and an absolute curvature maximum at \(s_0\). The normalized profile \(h(x)=k(s_0+x/M)/M\) has \(|h|\le1,\ h(0)=\pm1,\ h'(0)=0\), and \(\|h''+h^3/2\|_\infty\le(R+b\|q\|_\infty)/M^3=o(1)\). Thus \(h\) has constant sign and magnitude at least \(3/4\) on \([0,1/8]\) eventually. The unit tangents on this arc differ at its endpoints by a chord bounded below, because the net angular change has magnitude between \(3/32\) and \(1/8\). But \(N=X/p_0+o(1)\) uniformly by the position reconstruction \(X=qT+pN\). Over an arc of length \(1/(8M)\to0\), the endpoint positions differ by \(o(1)\), hence the endpoint normals and tangents also differ by \(o(1)\), a contradiction.

Finally use the fast arclength variable \(\tau=b^{1/3}s\) and write \(\kappa(\tau)=k(s)\). Differentiation gives \(F_s=kq-b(1+kp)\), hence the exact equation
\[
  (D_\tau^3+p_0)(\kappa+1/p_0)
       =-(p-p_0)\kappa+q\kappa/b
                   -\tfrac12 b^{-2/3}D_\tau(\kappa^3).
\]
The polynomial \(z^3+p_0\) has three simple roots, none on the imaginary axis. Its inverse on bounded smooth functions on the entire line is convolution with a Green kernel \(G\), and \(G,G'\in L^1\). For example partial fractions give a sum of stable half-line exponentials and unstable backward half-line exponentials. The jumps in \(G\) cancel because the rational symbol decays as \(z^{-3}\); the bounded homogeneous solution on the whole line is zero. The periodic functions above extend to the whole line. Convolving, transferring the derivative onto the kernel and using \(M=o(b^{1/3})\) gives
\[
 \|\kappa+1/p_0\|_\infty
 \le C\bigl(\|p-p_0\|_\infty+\|q\|_\infty/b+b^{-2/3}M^2\bigr)M
 =o(1) M.
\]
Absorption gives bounded \(M\) and then uniform \(\kappa\to-1/p_0\). In particular curvature has one strict sign eventually. One-sign rigidity forces those closed profiles to be circles, completing the contradiction. No compactness of periods, curvature derivatives before the estimates, or a priori bound on the turning number was used.

## Formal verification scope

In the independent SolitonClassification project, `RadiusPotential.lean` proves the derivative and integral identities in the first section from the four periodic support differential equations. It proves \(1\le2R^4\) for each positive cap with \(p^2+q^2\le R^2\), and proves that equality forces all four support coordinates to equal those of a centered circle. The circle classification includes both orientations and multiple coverings. The sequence arguments, the stress-window inequality, the unbounded-pitch limit and the resulting uniform strict gap are proved mathematically above. The existing formal one-sign theorem is applied at the end of each compactness argument. [Lean source](../../SolitonClassification/RadiusPotential.lean)
