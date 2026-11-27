# Laurent expansion at a meromorphic arclength pole

Let \(a>0\) and \(b\in\mathbb R\). Suppose a curvature germ \(k\) is meromorphic with a pole at \(s_0\), and satisfies the ordinary complex arclength equation on a punctured neighbourhood,
\[
2(kk^{(4)}-k'k''')+3k^2(k')^2+5k^3k''+k^6-2ak^2-2bk'=0.
\]
Then there exists \(c\in\{3i,-3i\}\) and a holomorphic germ \(R\) such that, for \(u=s-s_0\),
\[
k(s_0+u)=c/u+u^3 R(u).
\]
Consequently \(k''+2k^3/9\) extends holomorphically and vanishes at the pole.

For pole order \(m>1\), the exponent \(-6m\) of the sixth-power term is strictly below the exponents \(-2m-4\), \(-4m-2\), \(-2m\) and \(-m-1\) of the other terms. Its coefficient would have to vanish. Thus \(m=1\), and the coefficient at order \(-6\) gives \(c^2(c^2+4)(c^2+9)=0\).

Write \(uk=P(u)+u^6r(u)\), with \(r\) holomorphic and \(P=c+du+eu^2+fu^3+gu^4+hu^5\). For a term \(u^n[P+u^6r]\), ordinary differentiation sends its polynomial representative to \(nP+uP'\) and its exponent to \(n-1\). Multiplication adds exponents and multiplies polynomial representatives. These operations preserve a holomorphic remainder. The residual multiplied by \(u^6\) therefore has a polynomial representative divisible by \(u^6\).

When \(c^2=-4\), the coefficients of degrees two and three give
\[
36ce+108d^2=0,\qquad32cf+264de-70cd^3=0.
\]
This gives \(e=3cd^2/4\) and \(f=-4d^3\). After substitution the coefficients of degrees four and five give
\[
-504d^4+8a+2bc=0,\qquad cd(504d^4-4a)=0.
\]
At \(d=0\) the first equation yields \(8a+2bc=0\). If \(d\ne0\), the two equations yield \(4a+2bc=0\). Since \(c=\pm2i\) and \(a,b\) are real, both alternatives contradict \(a>0\).

When \(c^2=-9\), the coefficient at degree one is \(210cd\). Once \(d=0\), that at degree two is \(276ce\), and after \(e=0\), that at degree three is \(252cf\). Thus \(d=e=f=0\), giving the claimed Laurent expansion. Its leading singular terms in \(k''+2k^3/9\) cancel because \(2c+2c^3/9=0\); all remaining terms have exponent at least one.

The local result applies to arbitrary meromorphic germs solving the displayed equation. It requires neither a second complex period nor an assumption on the growth of \(k\) at infinity.
