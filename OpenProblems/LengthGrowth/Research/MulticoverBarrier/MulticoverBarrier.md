# A quantitative bending barrier for arbitrary covering number

Let \(m\ge1\) be the absolute turning number of a smooth immersed closed plane curve undergoing the free elastic flow \(X_t=-(k_{ss}+k^3/2)N\). Write \(B=\int k^2ds=2E\), \(L=\int ds\) and \(P=\sqrt{LB}\). Then
\[
 P(0)\le 2\pi m+\tfrac35
 \quad\Longrightarrow\quad
 P(t)\le P(0)\quad(t\ge0).
\]
In fact, while in this range \(LB\) decreases strictly on every noncircular slice. Equivalently, the allowed initial oscillation \(K_{\rm osc}=LB-(2\pi m)^2\) is \((12\pi/5)m+9/25\). The implication supplies a quarter-power upper bound for the physical length of this individual solution. Every closed similarity solution in the sublevel is an \(m\)-fold circle.

## A spatial inequality at a putative record

Reverse orientation when needed. Use the normalized arclength variable \(x=s\sqrt{B/L}\) of period \(P\) and put \(u=k/\sqrt{B/L}\), \(f=u''+u^3/2\). Then \(\int u=2\pi m,\ \int u^2=P\), where integration in the remainder of this argument is over one period with measure \(dx\). A nonnegative physical derivative of \(LB\) gives \(\int f^2\le\frac12\int uf\), by \(E'=-\int F^2ds,\ L'=\int kFds\).

Set \(v=u-1,\ V=\int v^2=2(P-2\pi m),\ A=\max |v|\), and \(r=4f-u-1\). Periodicity gives \(\int u''=0\). The exact polynomial identity
\[
 r^2+7v^2+4v^3-16(f^2-uf/2)=-8u''-4(u^2-1)
\]
shows that \(\int r^2\le (4A-7)V\). When \(V>0\), necessarily \(A\ge7/4\) and \(\|r\|_2\le(2A-3)\sqrt V\), since \((2A-3)^2-(4A-7)=4(A-2)^2\).
The differential identity \(4v''=r-v(2v^2+6v+5)\) yields
\[
 \|v''\|_2\le \tfrac12(A^2+4A+1)\sqrt V .
\]
Integration by parts and Cauchy–Schwarz then give
\(\|v'\|_2^2\le \sqrt V\,\|v''\|_2\).

Let \(x,y\) realize the maximum and minimum of \(v^2\). Its variation on each of the two arcs between them is at least \(A^2-\min v^2\). Summing both arcs, using \(\min v^2\le V/P\), and applying Cauchy–Schwarz gives
\[
 A^2\le V/P+\int |vv'|
       \le V/P+V\sqrt{(A^2+4A+1)/2}.
\]
Since \(P\ge2\pi m>6\), the assumed \(V\le6/5\) implies
\(5A^2-1\le 6\sqrt{(A^2+4A+1)/2}\). At \(A\ge7/4\) this is impossible: after squaring, the difference between the left and right squares is \(25A^4-28A^2-72A-17>0\). Writing \(x=A-7/4\), this polynomial is \(25x^4+175x^3+(3451/8)x^2+(5855/16)x+1465/256\).

Thus the derivative of \(LB\) is strictly negative throughout the punctured sublevel. The lower boundary \(LB=(2\pi m)^2\) is precisely constant curvature by equality in Cauchy–Schwarz. At every parallel upper boundary between the floor and the stated threshold, the derivative points strictly inward. Continuity and forward comparison therefore preserve every such upper bound, including equality at the initial upper boundary. For initial data at the floor, take the infimum of these bounds. On a similarity evolution \(LB\) is constant, so its initial slice in the sublevel has constant curvature.

For a physical quarter-power estimate, if \(L(t)>2L(0)\) choose \(s\le t\) with \(L(s)=L(t)/2\). The standard length–dissipation inequality \((L(t)-L(s))^2\le(t-s)(E(s)^2-E(t)^2)\) and \(2E(s)L(s)\le P(0)^2\) give \(L(t)^4\le4P(0)^4t\).

Andrews and Wheeler establish smooth convergence under sufficiently small scale-invariant curvature oscillation at each turning number. Their energy estimates involve universal constants after normalization to length \(2\pi m\). The assertion above gives a numerical coefficient and a direct sign for the derivative of the physical product. [Andrews and Wheeler, Theorem 1 and Lemmas 4–5](https://arxiv.org/html/2509.11129v2)
