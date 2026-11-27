# Quantitative attraction to the circle and the exact leading length constant

Let \(U=L\int k^2\,ds\), \(d=U-4\pi^2\), and use physical normal velocity \(-(k_{ss}+k^3/2)N\). Every smooth closed free elastic flow with \(d(0)\le36\) satisfies
\[
 -d'(t)\ \ge\ \frac{8\pi^2}{10^6}\frac{d(t)^2}{L(t)^4}.
\]
In particular \(d(t)\to0\). In combination with the small-curvature-oscillation theorem of Andrews and Wheeler, the length-normalized flow converges smoothly to a singly covered unit circle and
\[
 \lim_{t\to\infty}\frac{L(t)^4}{t}=2(2\pi)^4.
\]
The same hypothesis therefore determines the leading physical length constant. The proof of monotonicity and the explicit upper bound used below has a [complete formalization](DefectThirtySix.md).

## Quantitative estimate at fixed length

Freeze a time, rescale the curve to \(P=2\pi\), and orient with mean curvature one, as justified by the turning-number gap. All quantities in this paragraph refer to this rescaled slice. Set \(F=k_{ss}+k^3/2,\ B=\int k^2,\ D=\int F^2,\ J=\int kF,\ e=PD-BJ/2\). The [strict rate theorem](../../LengthGrowth/ActualFlow/DefectFlowSublevel.lean) gives \(e\ge0\) for noncircular slices, and a circle has \(e=0\). Put \(C=\int k^3,\ \sigma=\sqrt{B/P},\ u=k-1,\ V=\int u^2=d/P,\ Q=\int u_s^2,\ I_j=\int u^j\).

For \(\lambda=B/(4P)\), expansion gives \(\int(F-\lambda k)^2=e/P+\lambda^2 B\). Testing against one and using \(\sqrt{x+y}\le\sqrt x+\sqrt y\) gives \(2C\le B(1+\sigma)+4\sqrt e\). The dilation virial gives \(PD\ge B^2/4\), hence \(J\ge B/2-2e/B\). Expanding the centered cubic and quartic moments exactly as in the strict rate theorem, with the two displayed errors retained, gives
\[
 Q+\left(\frac52-\sigma-\frac1{\sigma+1}\right)V
 \le \frac12 I_4+4\sqrt e+\frac{2e}{B}.
\]
For \(d\le36\) the coefficient is at least \(69/100\) and \(V\le900/157\). Use \(3I_4^2\le V^3Q\). Completing the square in \(\sqrt Q\) gives \(I_4/2-Q\le V^3/48\). Consequently
\[
 \left(\frac{69}{100}-\frac{V^2}{48}\right)V
       \le 4\sqrt e+\frac{2e}{B},\qquad
 \frac{69}{100}-\frac{(900/157)^2}{48}>\frac1{200}.
\]
If \(\sqrt e<V/1000\), then \(\sqrt e<1\), and \(B=P+V>2\) gives \(2e/B\le\sqrt e\). This contradicts \(V/200\le5\sqrt e\). Thus \(e\ge V^2/10^6\). Under the dilation factor \(P/L\), the new \(e\) is \((L/P)^4\) times the physical \(LD-BJ/2\). Also \(V=d/P\), so \(-d'=2(LD-BJ/2)\) gives the stated inequality.

## Large physical times

Set \(\tau(t)=\int_0^t L(s)^{-4}\,ds\). The explicit length bound gives \(L^4\le \max(16L(0)^4,4U(0)^2t)\), hence \(\tau\to\infty\) by comparison with a logarithm. Along an interval where \(d>0\), integration gives \(1/d(t)\ge 1/d(0)+(8\pi^2/10^6)\tau(t)\). If \(d\) reaches zero, monotonicity and the global lower bound keep it there. Thus \(d\to0\) in all cases.

For a unit turning number \(d\) is precisely the scale-invariant curvature oscillation. At a sufficiently late time it falls below the positive constant in Andrews and Wheeler's Theorem 1. Restarting their result gives smooth convergence after rescaling to length \(2\pi\), up to the arclength parametrization. Their equation runs at twice the physical speed used here. A constant change of time preserves the convergence conclusion. [Andrews and Wheeler, Theorem 1 and proof of smooth convergence](https://arxiv.org/html/2509.11129v2#S1)

On the length-\(2\pi\) slice let \(J_*=-\int k_s^2+\tfrac12\int k^4\). Smooth convergence gives \(J_*\to\pi\). In physical time \(L'=J=(2\pi/L)^3 J_*\); hence \((L^4)'\to4(2\pi)^3\pi=2(2\pi)^4\). Time averaging proves the limit. This constant agrees with the exact expanding circle.

## A direct proof of the length constant

The leading constant also follows from scalar inequalities on the actual flow. This alternative uses the proved limit \(U\to4\pi^2\) and does not require smooth convergence of the normalized shape. In physical units set \(e=LD-BJ/2=-U'/2,\ Y=L^4 e,\ A=L^3J,\ S=L^4\). The dilation virial and Cauchy–Schwarz \(J^2\le BD\) give
\[
 A\ge 2\pi^2 U-\frac{2Y}{U},\qquad
 A^2\le UY+\frac{U^2}{2}A.
\]
For \(A>U^2/2\) the second inequality gives \((A-U^2/2)^2\le UY\), so in all cases \(A\le U^2/2+\sqrt{UY}\). The length bound gives \(L^4\le M(1+t)\) for a constant depending on the initial immersion. For \(t\ge T\ge0\),
\[
 \frac1t\int_T^tY(s)\,ds
 \le M\frac{1+t}{2t}\big[U(T)-U(t)\big].
\]
Taking a limit superior in \(t\), followed by \(T\to\infty\), gives \(t^{-1}\int_0^tY\to0\). Positivity and boundedness of \(U\), and Cauchy–Schwarz in time, also give \(t^{-1}\int_0^t\sqrt{UY}\to0\). Now \(S'=4A\), \(U\to4\pi^2\), and the time averages of both \(8\pi^2U\) and \(2U^2\) tend to \(32\pi^4\). Integrating the two bounds on \(A\) therefore proves \(S(t)/t\to32\pi^4\) directly.

## Verification

The independent length project verifies the physical quadratic dissipation gap, the decay \(d(t)\to0\), and the exact limit \(L(t)^4/t\to32\pi^4\) end to end from the actual normal flow and the single initial bound. In the formal limit proof the mean-value theorem on windows \([x,x^2]\) replaces integration of \(Y\). The two window bounds are divided by \(x^2\); the product drop tends to zero because both endpoint products have the same limit. The lower comparison tends to \(32\pi^4\), and the upper comparison is within \(4\eta\) for every fixed \(\eta>0\). Smooth convergence uses the external Andrews–Wheeler theorem as explained above. The unrestricted initial-value length problem remains open. [Exact physical limit](../../LengthGrowth/ActualFlow/DefectSharpLengthLimit.lean) · [Two-time estimates](../../LengthGrowth/ActualFlow/DefectLengthWindow.lean) · [Physical quadratic gap](../../LengthGrowth/ActualFlow/DefectPhysicalRate.lean) · [Attraction theorem](../../LengthGrowth/ActualFlow/DefectAttraction.lean) · [Independent project audit](SharpLength/Verification.json)
