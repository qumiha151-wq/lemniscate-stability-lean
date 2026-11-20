# Energy decay at logarithmic curvature-reversal thresholds

Let a single smooth closed immersed curve evolve by normal free elastic flow for all forward times. Write \(L\) for length, \(E=\frac12\int k^2\,ds\), \(\mathcal D=\int(k_{ss}+k^3/2)^2\,ds\), \(U=EL\), and \(d=\mathcal D L^2/(8E^3)\). Here \(n\) is one plus the minimal half-RMS index of the material slice. Its value bounds the number of subarcs needed to separate positive from negative excursions beyond half the root-mean-square curvature on every interval of at most one period.

The two-parameter static inequality for closed curves gives \(n^6d\ge c_0 U^2\) for a universal \(c_0>0\) whenever \(d\le1/16\). Every slice satisfies \(dU\ge\pi^2/2\) by the closed-curve virial inequality.

**Theorem.** Let \(b:[1,\infty)\to[1,\infty)\) be continuous and nondecreasing, with
\[
 \int_1^\infty \frac{dr}{r b(r)^3}=\infty .
\]
Suppose that some \(A,B,T\), with \(A>1\), \(B>0\) and \(T\ge0\), satisfy \(n(t)\le B U(t)^{1/3} b(U(t))\) whenever \(t\ge T\) and \(U(t)\ge A\). Then \(E(t)\to0\). With \(b(r)=(1+\log r)^\alpha\), \(0<\alpha<1/3\), there are constants \(c,C>0\) such that for all sufficiently large \(t\),
\[
 E(t)\le C\exp[-c(\log t)^{1-3\alpha}],\qquad
 L(t)\le C\sqrt t\exp[-c(\log t)^{1-3\alpha}].
\]
For \(\alpha=1/3\) the corresponding factors are \((\log t)^{-c}\).

**Proof.** On high-product slices combine the two-parameter estimate with the alternative \(d>1/16\). On all the other slices use \(dU\ge\pi^2/2\). Set \(c_1=\min(1/16,c_0/B^6,\pi^2/(2A))\). Since \(U\ge 2\pi^2\), this gives on the entire tail
\[
 d\ge c_1/b(U)^6 .
\]
The energy clock \(\xi=\log(E(T)/E(t))\) increases strictly, since \(E'=-\mathcal D<0\) on positive times. The inequality \(|L'|\le\sqrt{2E\mathcal D}\) implies
\[
 \frac{d\log U}{d\xi}\le \frac1{2\sqrt d}-1 \le (2\sqrt{c_1})^{-1}b(U)^3.
\]
For \(F(r)=\int_1^r [v b(v)^3]^{-1}\,dv\), the chain rule therefore gives \(F(U(t))\le F(U(T))+C\xi(t)\), including intervals of decreasing \(U\). If \(E_\infty>0\), the right side is bounded. Since \(F\) grows without bound, both \(U\) and \(L\) remain bounded. This contradicts \(\mathcal D L^3\ge4\pi^2 E^2\) and the finite dissipation budget.

For the quantitative assertion let \(z=1+\log(E(T)/E(t))\). When \(0<\alpha<1/3\), put \(p=1/(1-3\alpha)\). Direct integration of \(F\) gives \(\log U(t)\le C z^p\). At the endpoint \(\alpha=1/3\), it gives \(\log U(t)\le C\exp(Cz)\). For \(s\in[T,t]\), monotonicity of the energy bounds \(1+\log(E(T)/E(s))\le z\). Thus both \(L(s)\) and \(b(U(s))^6\) are bounded by \(\exp(C z^p)\), or by \(\exp(C\exp(Cz))\) at the endpoint, after enlarging constants. Integrating
\[
 \mathcal D(s)\ge 8 c_1 E(t)^3/(L(s)^2 b(U(s))^6)
\]
over \([T,t]\) and using \(\int_T^t\mathcal D\le E(T)\) gives respectively \(\log(1+t)\le C z^p\) and \(\log(1+t)\le C\exp(Cz)\). Here the factor \(E(t)^{-3}\) contributes at most a constant times \(z\) to the logarithm. Rearranging proves the two stated energy bounds.

The physical secant gives \(L(t)\le L(s)+\sqrt{t-s}E(s)\). At \(s=\sqrt t\) the same secant from time zero gives \(L(s)=O(t^{1/4})\). This is absorbed into the claimed right side of the length estimate in both cases. Applying the energy bound at \(s=\sqrt t\) completes the assertion.

If \(E_\infty>0\), for every admissible \(b\) there is a sequence \(t_j\to\infty\) along which both \(U(t_j)\to\infty\) and \(n(t_j)/(U(t_j)^{1/3}b(U(t_j)))\to\infty\). Indeed failure to find \(t_j\ge j\) with \(U(t_j)\ge j\) and this ratio greater than \(j\) for any single \(j>1\) implies the theorem's hypothesis. Examples of admissible \(b\) include the cube root of any finite product of successive logarithms for large \(r\), extended with values at least one and monotonically to \([1,\infty)\). This theorem concerns a single flow and leaves open whether the required oscillations are dynamically possible for general data.

**Verification.** CriticalOsgoodFlow.lean proves energy decay for the actual minimum half-RMS index given an unbounded differentiable primitive with the specified derivative on \(u>1\). It also constructs the logarithmic primitive at \(\alpha=1/3\). CriticalEndpointFlow.lean gives both power rates in the special case \(b=1\). CriticalLowDissipationMaterial.lean supplies the geometric two-parameter inequality. The stretched-exponential and inverse-logarithmic rates in this note and the iterated-logarithm applications are analytic consequences.
