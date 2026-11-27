# Uniform separation from the circle's sharp growth coefficient at high product

For a smooth closed planar immersion let \(L\) be its period in arclength, \(E=\tfrac12\int k^2ds\), \(F=k_{ss}+k^3/2\), \(D=\int F^2ds\) and \(U=EL\). Define \(\eta=L U'/E^3\) using the physical free elastic flow through the slice. Equivalently, \(U'=E\int kF\,ds-LD\). Write \(B=U(1/2-\eta)\). All three numbers \(U,\eta,B\) are unchanged by a spatial dilation with its corresponding time scaling.

The global sharp inequality is \(B\ge\pi^2\). The once-traversed expanding circle gives equality. The following estimates identify a gap away from its energy–length product:
\[
 \begin{split}
 B\le11 \quad&\Longrightarrow\quad
 B-\pi^2\ \ge\ \frac{\pi^2}{2916B}
      \left(\max\!\left\{0,1-\frac{2B}{U}\right\}\right)^2,              \tag{1}\\
 U\ge200 \quad&\Longrightarrow\quad B\ \ge\ \pi^2+\frac{1}{20000}.
 \end{split}
\]
In particular, \(B_j\to\pi^2\) for any sequence of closed immersions forces \(U_j\to2\pi^2\). There are no covering-number or sign-of-curvature restrictions. There is no universal improvement to the power of \(U^{-1}\) in \(1/2-\eta\) in the known fixed-turn small-angle-wave sequences.

## Support and normalization

The growth residual \(R=F-Ek/(2L)\) has derivative primitive \(W=(k^2/2-E/(2L))T+k_sN\), namely \(W_s=RN\). For every complex translation \(z\) and every real \(\omega\), put \(\psi_{z,\omega}=N\cdot((1+i\omega)X-z)\). Pair \(W\) with \((1+i\omega)X-z\) and integrate by parts over a period. The curvature-slope term \(\omega k_s\) has zero integral, leaving
\[
 \int R\psi_{z,\omega}\,ds=-E/2,\qquad
 \int R^2ds=\frac{E^3}{L^2}(1/2-\eta).
\]
Consequently the variance about arbitrary rigid motions gives
\[
 (1/2-\eta)\inf_{z,\omega}\int\psi_{z,\omega}^2\,ds\ge L^2/(4E).
\]
At the arclength centroid \(z\) and \(\omega=0\), the support moment is at most the full position moment. Periodic Wirtinger bounds the latter by \(L^3/(4\pi^2)\), since \(|X_s|=1\). This gives \(B\ge\pi^2\). Similarly, a containing disk of radius \(r\) gives \((1/2-\eta)r^2\ge L/(4E)\), also for the smallest enclosing radius.

Dilate to root-mean-square curvature one. The new arclength period is \(P=\sqrt{2U}\), the energy is \(P/2\), and \(R=F-k/4\). Write \(\langle f\rangle=P^{-1}\int_0^P f\,ds\). Then \(B=4P\int R^2ds\), so \(\int|R|ds\le\sqrt B/2\). Write \(M=\max|k|\). For \(B\le11\), the corrected stress \(W=(k^2/2-1/4)T+k_sN\) has total variation less than two. The usual lower bound \(U\ge2\pi^2\) gives \(P\ge2\pi>6\). Integration of \(k k_{ss}\) by parts gives
\[
 \langle |W|^2\rangle
 =\tfrac34\langle k^4\rangle-\tfrac7{16}-\langle kR\rangle
 \le \tfrac34 M^2 .
\]
Indeed \(\langle k^2\rangle=1\) and \(|\int kR|\le \sqrt B/2<2\), so \(|\langle kR\rangle|<1/3\). At some point \(|W|\le M\), and hence \(\|W\|_\infty\le M+2\). At a maximum of \(|k|\), \(M^2/2-1/4\le |W|\le M+2\), which implies \(M<4\). Also \(\max|k_s|\le\|W\|_\infty<6\). These bounds hold on the full RMS period even when that period becomes arbitrarily long.

## Radial projection controls curvature

Take \(Y=(X-z)/P\), still using RMS arclength \(s\); here \(z\) is the arclength centroid. Set \(u=Y\cdot T,\ p=Y\cdot N,\ h=\langle u^2\rangle^{1/2}\). Both scalar products have absolute value at most one: \(|X(s)-z|\le P\) follows by averaging \(|X(s)-X(w)|\le P\) in \(w\). The orthonormal frame gives \(|Y|^2=u^2+p^2\). The residual virial becomes \(\int R p\,ds=-1/4\). By Cauchy–Schwarz and the centroid Wirtinger estimate,
\[
 \langle p^2\rangle\ge1/(4B),\qquad
 h^2\le\frac1{4\pi^2}-\frac1{4B}.
                                                               \tag{2}
\]
Since \((|Y|^2)'=2u/P\), the oscillation of \(|Y|^2\) is at most \(2h\). Thus everywhere \(|Y|^2\ge1/(4B)-2h\).

The Frenet equations give the exact derivatives
\[
 u'=kp+1/P,\qquad p'=-ku,\qquad u''=k_s p-k^2u .
\]
The global slope and curvature bounds give \(\|u''\|_\infty\le22\). Periodicity and integration by parts yield \(\langle (u')^2\rangle\le22h\). Since \(\langle u'\rangle=0\), we have
\[
 \langle k^2p^2\rangle
   =\langle (u')^2\rangle+P^{-2}\le22h+P^{-2}.
\]
The pointwise lower bound on \(|Y|^2\) and \(\langle k^2\rangle=1\) also give
\[
 \langle k^2p^2\rangle
  =\langle k^2|Y|^2-k^2u^2\rangle
  \ge(4B)^{-1}-2h-16h^2.
\]
Therefore \((4B)^{-1}-P^{-2}\le24h+16h^2\le27h\), since \(h\le1/(2\pi)<1/6\). Substituting (2) and \(P^2=2U\) gives (1).

For the displayed numerical consequence, suppose \(P\ge20,\ B\le11\). The inequalities give \((4B)^{-1}>1/50,\ P^{-2}\le1/400\). Hence \(h\ge(1/50-1/400)/27>1/2000\). Equation (2) gives \(B-\pi^2\ge4B\pi^2h^2>4\cdot3^4/2000^2>1/20000\). If \(B>11\), use \(\pi^2<10\) directly.

If \(B_j\to\pi^2\), (1) gives \(\max\{0,1-2B_j/U_j\}\to0\); hence \(\limsup U_j\le2\pi^2\). The universal lower bound proves \(U_j\to2\pi^2\). In particular sharp equality requires the minimal energy–length product. In conjunction with the equality case of periodic Wirtinger, this leaves only the once-traversed circle up to similarities and orientation: normalize length to one and apply Wirtinger to the unit tangent of mean zero. Equality requires \(T=A\cos(2\pi s)+B_0\sin(2\pi s)\); \(|T|=1\) forces \(A,B_0\) to be orthonormal.

The optimized support identity, the universal \(\pi^2\) estimate for the physical derivative, and the bound on the smallest enclosing radius have independent Lean proofs. The new formal results check the quantitative centroid-radius oscillation estimate and give a direct proof of exact equality: at a positive time on a genuine flow the bound is attained if and only if \(EL=2\pi^2\), and attainment gives an explicit once-traversed circle on the original material labels. Formula (1) and its limiting implication are written proofs. [Quantitative annulus estimate](../../LengthGrowth/ActualFlow/SaturationAnnulus.lean) · [Equality on the physical flow](../../LengthGrowth/ActualFlow/PhysicalEqualityCircle.lean)
