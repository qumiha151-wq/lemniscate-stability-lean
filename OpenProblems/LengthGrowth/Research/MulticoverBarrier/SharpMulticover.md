# Explicit attraction and the sharp length coefficient at every nonzero turning number

Let \(\gamma\) be a smooth closed planar immersion evolving by free elastic flow, with multiplicity of turning \(m\ge1\) in either orientation. Define \(E=\tfrac12\int k^2ds,\ L=\int ds,\ M=2\pi m,\ P=\sqrt{2EL}\), and \(\delta=P^2-M^2\). Suppose the initial curve satisfies
\[
\delta(0)\le \frac{12\pi}{5}m+\frac9{25}.
\]
On this sublevel the actual evolution satisfies
\[
\delta(t)\le\delta(0)(1+t)^{-\lambda},\qquad
\lim_{t\to\infty}\frac{L(t)^4}{t}=2(2\pi m)^4,
\quad
\lambda=\frac{M^4}{500[(2L(0))^4+4P(0)^4+1]}.
\]
The rate uses the paper's original time coordinate. The limit gives the coefficient \(2^{1/4}(2\pi m)\) of \(t^{1/4}\). In the single-turn case the separate defect-36 theorem has a wider initial sublevel. The inclusion radius above grows linearly in \(m\) as a curvature-oscillation threshold.

## The quantitative loss

Orient the curve so that its signed curvature integral is positive. Use dimensionless RMS arclength of period \(P\) and RMS curvature \(u\), so \(\int u=M,\ \int u^2=P\). Put \(f=u''+u^3/2,\ J=\int f^2-\tfrac12\int uf,\ v=u-1,\ V=\int v^2=2(P-M)\), and \(A=\max|v|\). All integrals in this paragraph use one full RMS period. We claim \(J>V/1000\) whenever \(0<V\le6/5\). If \(J\le V/1000\), the integrated identity for \(r=4f-u-1\) gives
\[
0\le\|r\|_2^2=16J-7V-4\int v^3\le(4A-7+2/125)V .
\]
Thus \(A\ge87/50\). One has \((2A-3+1/50)^2\ge4A-7+2/125\), by expanding the difference about \(A=2\) and using \(A\ge87/50\). The differential identity \(4v''=r-v(2v^2+6v+5)\) implies
\[
\|v''\|_2\le K\sqrt V,\qquad K=\frac{A^2+4A+1}{2}+\frac1{200}.
\]
Integrating by parts and using the variation of \(v^2\) along both complementary arcs as in the strict barrier gives \(A^2\le V/P+V\sqrt K\). Consequently \(5A^2-1\le6\sqrt K\). Both sides are nonnegative, and the squared difference equals \(25A^4-28A^2-72A-859/50\). At \(A=87/50+x\) this is
\[
25x^4+174x^3+\frac{21307}{50}x^2+\frac{446703}{1250}x+\frac{481561}{250000}>0 ,
\]
a contradiction.

Let \(D=\int F^2ds\) be the actual dissipation and \(F=k_{ss}+k^3/2\). RMS rescaling yields \(Y=L^4(LD-EL')=P^5J\). Since \(P\ge M\), the estimate gives \(Y\ge M^4\delta/1000\), strictly for positive \(\delta\). At the zero floor the physical product is stationary at every positive time where it attains that floor. Write \(B=(2L(0))^4+4P(0)^4+1\). The preceding invariant sublevel bound gives \(L^4\le B(1+t)\). Since \(\delta'=-2(LD-EL')\), differentiating \(\delta(t)(1+t)^\lambda\) gives the stated power decay.

## The length coefficient

For signed turning \(S=\int k\,ds\), let \(Z=\gamma+(L/S)N\) at a fixed time. Its arclength derivative is \(Z_s=(1-Lk/S)T\), and
\[
\int (1-Lk/S)^2ds=L\delta/S^2 .
\]
It follows that the entire curve lies in the disk centered at \(Z(0)\) with radius \(r=(L/M)(1+\sqrt\delta)\). Indeed, integrate \(Z_s\) and use Cauchy–Schwarz, then add \(|L/S|\) to recover \(\gamma\). The dilation identity \(\int F\langle N,\gamma-z\rangle ds=-E\) and \(\int k\langle N,\gamma-z\rangle ds=-L\) give \(E^2\le DLr^2\) and \(L\le2Er^2\). Therefore \(E\le2Dr^4\).

Set \(U=2EL,\ A=L^3L',\ e=LD-EL'\ge0,\ Y=L^4e\). The disk estimate gives \(U M^4/[2(1+\sqrt\delta)^4]\le U A+2Y\). Also Cauchy–Schwarz gives \(A^2\le UY+(U^2/2)A\). Since \(U\ge1\), for every \(\eta>0\),
\[
\frac{2M^4}{(1+\sqrt\delta)^4}-8Y
 \le (L^4)'
 \le 2U^2+4\eta+\frac{U}{\eta}Y.
\]
Integrate on \([T,t]\). The signed defect decreases, \(L(s)^4\le B(1+t)\), and \(\int_T^t e=E(T)L(T)-E(t)L(t)\). Thus the terms involving \(Y\), divided by \(t\), are bounded by a fixed multiple of \((1+1/t)[E(T)L(T)-E(t)L(t)]\) for each fixed \(\eta\). Taking \(T=\sqrt t\) sends these terms to zero, since \(2EL\to M^2\). Also \(L(\sqrt t)^4/t\to0\). The lower coefficient tends to \(2M^4\) and the upper coefficient tends to \(2M^4+4\eta\). Letting \(\eta\downarrow0\) proves the limit.

Andrews and Wheeler prove smooth convergence from sufficiently small curvature oscillation. Here the numerical oscillation sublevel, the power bound and the physical length limit follow directly from the flow identities. [Andrews and Wheeler, Theorem 1 and Lemmas 4–5](https://arxiv.org/html/2509.11129v2)

