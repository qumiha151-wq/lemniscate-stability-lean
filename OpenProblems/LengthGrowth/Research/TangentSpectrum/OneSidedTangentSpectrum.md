# A one-sided Fourier obstruction to super-fourth-root length growth

Consider one smooth closed immersed planar free elastic flow. Set \(E=\frac12\int k^2\,ds\), \(L=\int ds\) and \(U=EL\). Identify the plane with \(\mathbb C\). On each time slice parameterize the directed unit tangent \(T\) by \(u=s/L\in\mathbb R/\mathbb Z\), and let \(c_n=\int_0^1T(u)e^{-2\pi inu}\,du\). The arbitrary arclength origin and ambient rotation affect only the phases of the coefficients. The turning number \(m\) is constant on this flow.

Define the two nonnegative quantities
\[
 B_+(t)=\sum_{n>0}n|c_n(t)|^2,\qquad
 B_-(t)=\sum_{n<0}|n|\,|c_n(t)|^2 .
\]
If either quantity is bounded on a time tail, then \(L(t)\le C(1+t)^{1/4}\) on the whole forward flow. More precisely, at every positive time with \(U'\ge0\) one has
\[
 B_++B_-\ \ge\ \frac{\sqrt2}{32\pi}U^{1/3},
 \qquad
 \min(B_+,B_-)\ \ge\ \frac{\sqrt2}{64\pi}U^{1/3}-\frac{|m|}{2}.
\]
As a result, an orbit with unbounded product must have both signed parts unbounded, simultaneously at arbitrarily late record times. A bound on one side by \(B\) on the tail gives
\[
 \sup_{t\ge0} U(t)\le
 \max\left\{\max_{0\le t\le t_0} U(t),1,
       \big[(32\pi/\sqrt2)(2B+|m|)\big]^3\right\}.
\]

## Record estimates

Write \(K(u)=Lk(Lu)\), \(H(u)=L^3(k_{ss}+k^3/2)(Lu)\), and use the unweighted unit-interval norms. Then \(\|K\|_2^2=2U\) and \(K''=H-K^3/2\). The genuine evolution laws \(E'=-\int F^2\,ds\) and \(L'=\int kF\,ds\) give
\[
 L^4 U'=U\int_0^1KH\,du-\|H\|_2^2,\qquad F=k_{ss}+k^3/2 .
\]
Thus \(U'\ge0\) gives \(\|H\|_2\le\sqrt2\,U^{3/2}\). The previously proved pointwise stress inequality \(|k|^6\le 2^{24}E\int F^2\,ds\) now gives
\[
  |K|^6\le2^{24}U\|H\|_2^2 \le 2^{25}U^4 .
\]
For \(A=2^{25/6}\) we have \(\|K\|_\infty\le A U^{2/3}\). Since \(U>0\), the record identity also gives \(\int KH\ge0\). Periodic integration by parts yields \(\|K'\|_2^2=-\int KK''=\frac12\int K^4-\int KH\). The Frenet identities \(T'=iKT\) and \(T''=(iK'-K^2)T\) therefore imply
\[
 \|T'\|_2^2=2U,\qquad
 \|T''\|_2^2=\tfrac32\int K^4-\int KH
 \le\tfrac32\|K\|_\infty^2\|K\|_2^2
 \le3A^2 U^{7/3}\le1024\,U^{7/3}.
\]
The last numerical bound uses \(A^2=(2^{25})^{1/3}<340\).
## Fourier moments

Let \(M_q=\sum |2\pi n|^q|c_n|^2\) for \(q>0\). Parseval gives \(M_2=2U\) and \(M_4\le1024U^{7/3}\). Hölder gives \(M_2^3\le M_1^2 M_4\), hence \(M_1\ge(\sqrt2/16)U^{1/3}\). The smooth Fourier series and the Frenet equation give the signed identity including its normalization,
\[
 2\pi i\sum_n n|c_n|^2=\int_0^1\overline T T'\,du
   =i\int_0^1K\,du=2\pi i m.
\]
Consequently \(B_+-B_-=m\) and \(B_++B_-=M_1/(2\pi)\), proving the claimed estimates. If \(U\) is unbounded, first crossings give arbitrarily late times with \(U'\ge0\) and arbitrarily large \(U\). Conversely, a bounded \(U\) implies fourth-root length growth by the established single-flow equivalence in this project.

The same calculation gives a family of compactness criteria below the continuous embedding threshold. For \(1/4<\alpha<1\), Hölder interpolation gives
\[
 \|T\|_{\dot H^\alpha}
 \ge (2U)^{(2-\alpha)/2}
     (1024 U^{7/3})^{-(1-\alpha)/2}
 = 2^{(2-\alpha)/2}32^{-(1-\alpha)}
   U^{(4\alpha-1)/6}.
\]
The same Fourier convention applies to this seminorm. Thus a bounded normalized tangent seminorm with any such exponent on even a time tail suffices. The argument gives no positive growth exponent at \(\alpha=1/4\). It leaves the unrestricted one-flow question open.
