# A positive limiting energy requires force concentration on infinitely many shrinking stress bands

Consider any one global smooth immersed closed free elastic flow in the plane. Use the material normal gauge, \(k\) for signed curvature, \(p=k_s\), \(F=k_{ss}+k^3/2\), \(r=(p^2+k^4/4)^{1/2}\), and \(E_\infty=\lim_{t\to\infty}\frac12\int k^2ds\). For every positive starting time \(T\), define
\[
 \nu_j(T)=\int_T^\infty\int_{\{2^{-j-1}<r\le2^{-j}\}}
                         \frac{F^4}{r^3}\,ds\,dt,\qquad j\in\mathbb Z .
\]
Then
\[
             E_\infty\ \le\ 15\limsup_{j\to\infty}\nu_j(T).                 \tag{1}
\]
Each individual band has finite action. For example, \(\nu_j(T)\to0\) suffices for energy decay to zero, even when \(\sum_j\nu_j(T)\) diverges. Bounded \(|F|/r^{3/2}\) on the positive-stress part of a time tail also suffices, by the ordinary energy dissipation identity. If \(E_\infty>0\), arbitrarily small stress bands on **every** time tail must have a fixed amount of the fourth-power force action. The ordinary masses \(\int_{B_j}F^2\,ds\,dt\) of these disjoint bands tend to zero. In particular the dissipation-weighted mean of \(F^2/r^3\) becomes unbounded along a subsequence. This estimates energy decay on one flow; it does not settle the general length-growth question.

The Lean project checks the [scale coefficient differentiation and local quadratic bounds](../../LengthGrowth/ActualFlow/StressScaleCurrent.lean), the [periodic integration by parts in the physical material parameter](../../LengthGrowth/ActualFlow/PhysicalAnnularFlux.lean), and the [two-sided band sum and its limit with constant 15](../../LengthGrowth/ActualFlow/StressAnnularTransfer.lean). The evolution of the corrected length and the passage between the time and scale limits in the argument below are written proofs.

## An exact current in the regularization parameter

Put \(R=(r^2+a^4)^{1/2}\), \(Q=k^2F_{ss}-2kpF_s\), and
\[
 \Lambda_a=\tfrac12\int (k^2/R-k^3F/R^3)\,ds,\qquad Z_a=a\int_a^\infty\Lambda_b\,db .
\]
The two coefficient derivatives in the [regularized stress identity](StressScaleLength.md) give an exact conservation law in the scale \(a\):
\[
 \frac{d}{dt}\Lambda_a =
 \partial_a\int\frac a{R^3}\big[(a^4-k^4/4)F^2-FQ/2\big]\,ds.
\]
Indeed \(\partial_a[-a/(2R^3)]=(5a^4-r^2)/(2R^5)\). For the other coefficient, put \(u=k^4/4,\ v=p^2\); its derivative has numerator \(-u(u+v)+(10u+5v)a^4-a^8\) over \(R^5\), as required. The current vanishes as \(a\to\infty\). Differentiation under integrals is valid on compact positive time windows by smoothness, periodicity and the \(O(b^{-2})\) bound for the derivative of \(\Lambda_b\) as \(b\to\infty\). Therefore
\[
 Z_a'=a^2\int R^{-3}\big[(k^4/4-a^4) F^2+FQ/2\big]\,ds .                \tag{2}
\]

Integrate the \(F F_{ss}\) term in (2) by parts on the arclength circle. Since \(R_s=pF/R\), the derivative terms, before the factor \(a^2\), are
\[
 -\frac{k^2F_s^2}{2R^3}-\frac{2kpFF_s}{R^3}
       +\frac{3k^2pF^2F_s}{2R^5}.
\]
Writing \(A=k F_s/R^{3/2}\), \(B=-2pF/R^{3/2}+3kpF^2/(2R^{7/2})\), these terms are \(-A^2/2+AB\le B^2/2\). Use \((u+v)^2/2\le u^2+v^2\), \(k^4/4\le r^2\), \(p^2\le r^2\), \(k^2\le2r\), and \(r\le R\). With \(w(x)=x^2/(1+x^2)^{3/2}\) the result is
\[
       Z_a'\ \le\int_{\{r>0\}} w(r/a^2)\left(5F^2+\tfrac92 F^4/r^3\right)ds.   \tag{3}
\]
The coefficient for \(F^4/r^3\) initially has \(x^6/(1+x^2)^{7/2}\), bounded by \(w(x)\). At \(r=0\) the remaining integrand of (2) after integration by parts is nonpositive. This one-sided bound contains no derivatives of \(F\).

## The order of the time and scale limits

For each fixed \(a>0\), \(Z_a(t)\to E_\infty\). In fact \(b^2\Lambda_b(t)\to E_\infty\) for each \(b\ge a\), and its absolute value is at most \(E(t)+\frac12 a^{-4}\int |k^3 F|ds\), bounded on the tail by the [force estimates](../ForcePersistence/ForceDissipationPersistence.md). Integrate against \(a b^{-2}db\).

Conversely, at **each fixed finite smooth slice**, \(Z_a(T)\to0\) as \(a\downarrow0\), including ones with degenerate or infinitely many curvature zeros. To justify domination, let \(g=k_s\) on its arclength circle. On a component \(I\) of \(\{g'\ne0\}\), \(g\) is monotone; the integral of \(|g'|/\sqrt{|g|}\) on \(\{g\ne0\}\cap I\) is at most \(4\sqrt{\operatorname{osc}_I g}\), by integration of \(1/\sqrt{|u|}\) between endpoint values. Periodicity supplies a zero of \(g'\); both endpoints of each such interval have \(g'=0\). Consequently \(\operatorname{osc}_I g\le\|g''\|_\infty |I|^2\). Summing gives a finite bound \(4L\sqrt{\|g''\|_\infty}\). Points where \(g=0,\ g'\ne0\) are isolated. Together with \(r\ge |p|\) and \(r\ge k^2/2\), this proves \(\int_{\{r>0\}} |F|/\sqrt r\,ds<\infty\). The second integrand of \(b^2\Lambda_b(T)\) is bounded in absolute value there by \(C|F|/\sqrt r\); the first is bounded by \(k^2/2\). Both vanish where \(r=0\) and both tend pointwise to zero as \(b\downarrow0\). Thus \(b^2\Lambda_b(T)\to0\). That function is bounded also for large \(b\); splitting \(a\int_a^\infty b^{-2}[b^2\Lambda_b(T)]db\) at any fixed small \(b\) proves the claim.

## Summing the dyadic bands

Integrate (3) from \(T\) to infinity and take \(a^2=2^{-j}\). Since \(\int_T^\infty\int F^2ds\,dt<\infty\), bounded convergence sends the \(F^2\) contribution to zero. The stress is uniformly bounded from \(T\) onwards and converges uniformly to zero; hence only finitely many very large-stress bands are present, and each fixed positive band is reached only in a bounded time interval. For the remaining term use \(w(u)\le\min(u^2,1/u)\) for \(u>0\). On band \(k\ge j\) this is bounded by \(4^{j-k}\); on band \(k<j\) it is bounded by \(2^{k+1-j}\). The total of the weights is \(4/3+2=10/3\). If \(\limsup\nu_k=\infty\), (1) holds in the extended sense. Otherwise for every \(\epsilon>0\) the far positive-index tail is bounded by \(\limsup\nu_k+\epsilon\), and the finitely many earlier nonempty bands contribute a quantity tending to zero. Equation (1) follows with coefficient \((9/2)(10/3)=15\). All spacetime integrals here use the evolving physical arclength measure.
