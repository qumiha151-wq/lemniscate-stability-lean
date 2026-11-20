# Sharpness of the static error for a bounded number of curvature sign changes

There exist a fixed integer \(N_*\) and a sequence of smooth closed immersed curves of turning number one having at most \(N_*\) genuine changes of curvature sign, with \(E L\to\infty\). At the initial time of the free elastic flow from each curve, \((E L)'>0\). The examples also realize the order of both pointwise error terms used in [the finite-sign-change length estimate](FiniteSignChanges.md).

Use arclength \(s\), \(P=L\), \(F=k_{ss}+k^3/2\), \(Q=\int k^2=2E\), \(D=\int F^2\), and \(V=\int kF=L'\). Write the quantities after scaling to length one as
\[
 b=PQ,\qquad d=P^5 D,\qquad v=P^3 V .
\]
For the constructed sequence, two finite, strictly negative constants \(j,h\) satisfy
\[
 \sqrt b\,\frac{d-bv/2}{b^3}\longrightarrow j,\qquad
 \frac{\sqrt d-b^{3/2}/2}{b}\longrightarrow h .
\]
In particular a unit-length lower bound \(\sqrt d\ge b^{3/2}/2-o(b)\) fails in the fixed-\(N_*\) class. At the same points \(d\sqrt{EL}/d\log(E(0)/E)\to-\sqrt2\,j>0\), where this denotes the instantaneous right derivative along each corresponding flow. These facts leave open the integrated, long-time behavior of a single flow.

## A trigonometric packet

In \(x=s/\sqrt2\), let
\[
 K(s)=a(\cos x+\tfrac1{10}\cos 3x),\qquad
 a=\sqrt{200/101},\qquad p=2\pi\sqrt2.
\]
Averages \(\langle\cdot\rangle\) over one \(s\)-period obey \(\langle K\rangle=0\) and \(\langle K^2\rangle=1\). This wave has two simple sign changes per period since \(\cos x+\frac1{10}\cos3x=\cos x(7/10+(2/5)\cos^2x)\). Its force \(\mathcal F=K''+K^3/2\) is
\[
 \mathcal F=\frac a{4040}
       (1340\cos x-215\cos3x+330\cos5x+30\cos7x+\cos9x).
\]
The coefficients follow by expanding \(K^3\) with the product-to-sum identity. Orthogonality gives the exact averages
\[
 \langle K\mathcal F\rangle
   =\frac{a^2}{2\cdot4040}(1340-215/10)
   =\frac{13185}{40804},\qquad
 \langle\mathcal F^2\rangle
   =\frac{a^2(1340^2+215^2+330^2+30^2+1)}
           {2\cdot4040^2}
   =\frac{975813}{8242408}.
\]
Thus \(\langle\mathcal F^2-K\mathcal F/2\rangle=-44484/1030301<0\), and \(\langle\mathcal F^2\rangle<1/4\).

## Smooth joins, exact position closure and the fixed sign count

Build a single block in arclength with a \(+1\) plateau of length \(T_+\), a packet of \(m\) full periods of \(K\), and a \(-1\) plateau of length \(T_-\). The two packet ends are joined smoothly to \(+1\) at the positive maximum \(x=0 \bmod 2\pi\). For an explicit construction, on a short interval immediately before the packet use a smooth cutoff equal to zero near its left endpoint and one near its right endpoint to interpolate \(1+\chi(s)(K(s)-1)\). Choose the interval within the region \(K>0\). Reflect this bridge after the last period. Use an independent smooth monotone step from \(+1\) to \(-1\) before the negative plateau, and the reversed step after it. Both steps can be flat at their ends and have exactly one transverse zero. The block starts and ends on \(+1\). The four bridges have fixed profiles, lengths and integrals independent of \(m,T_\pm\).

The \(m\) full periods contribute zero to signed turning. Let \(\sigma\) be the integral of curvature on the four bridges. Take \(T_-=T\), \(T_+=T+\pi-\sigma\), with \(T\) sufficiently large to keep both lengths positive. The block has signed turning \(\pi\). Repeat it twice and denote its full length by \(P\). The resulting smooth, \(P/2\)-periodic curvature has total signed turning \(2\pi\). Integrate the tangent \(X'(s)=(\cos\theta(s),\sin\theta(s))\) with \(\theta(s)=\int_0^s k\). Since \(X'(s+P/2)=-X'(s)\), the position closes exactly. The unit-speed immersed curve has at most \(N_*=4m+4\) genuine curvature sign changes, independent of \(T\).

## The two limiting deficits

Over the full closed slice write
\[
 Q=P+q,\qquad V=P/2+v_0,\qquad D=P/4+d_0.
\]
For fixed \(m\), \(q,v_0,d_0\) are independent of \(T\), because every unit of either plateau contributes the corresponding background values \(1,1/2,1/4\). Each full packet period contributes zero to \(q\). Hence for
\[
 j=d_0-v_0/2-q/4,\qquad h=d_0-3q/4
\]
the contributions of each of the \(2m\) packet periods are respectively \(p\langle\mathcal F^2-K\mathcal F/2\rangle<0\) and \(p(\langle\mathcal F^2\rangle-1/4)<0\). All bridge contributions are independent of \(m\). Choose one finite \(m\) large enough that both \(j,h\) are negative, and keep it fixed. Then as \(T\to\infty\), \(P\to\infty\), and direct multiplication yields
\[
 \begin{split}
 D-\frac{Q}{2P}V&=j-\frac{qv_0}{2P},\\
 D-\frac{Q^3}{4P^2}&=h-\frac{3q^2}{4P}-\frac{q^3}{4P^2}.
 \end{split}
\]
In the normalization to length one, \(d-bv/2=P^5(D-QV/(2P))\) and \(d-b^3/4=P^5(D-Q^3/(4P^2))\). Since \(b=P(P+q)\sim P^2\), dividing gives the first limit in the statement and \(\sqrt b(d/b^3-1/4)\to h\). Factoring the latter difference of squares yields the second stated limit.

For the actual flow from any such immersion, \(E'=-D\), \(L'=V\). Thus \((EL)'=-P(D-QV/(2P))>0\) for all sufficiently large \(T\). If \(\xi=\log(E(0)/E(t))\), then
\[
 \frac{d\sqrt{EL}}{d\xi}
   =-\frac{\sqrt{EL}}{2}\frac{D-QV/(2P)}{D}
   \longrightarrow -\sqrt2\,j>0
\]
at the initial points along this sequence since \(\sqrt{EL}\sim P/\sqrt2\) and \(D\sim P/4\). These are instantaneous geometric data. The construction shows why an improvement from logarithmic to exact quarter-power growth for bounded-sign-change solutions requires information beyond an improvement of these static errors on every slice.
