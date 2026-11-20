# Length growth with bounded curvature sign changes

Consider a single smooth closed planar free elastic flow. Suppose that after
some time the number of genuine changes of sign of its signed curvature on
the parameter circle is at most \(N\). Zeroes with the same sign on either
side can be arbitrarily numerous. Then
\[
 L(t)\le C_{\gamma,N}(1+t)^{1/4}\bigl(1+\log(2+t)\bigr).
\]
In particular \(L(t)=O_\varepsilon(t^{1/4+\varepsilon})\) for every
\(\varepsilon>0\). The following proof concerns the actual flow and uses
static estimates on its slices. The bounded-sign-change hypothesis has
not been proved for arbitrary initial curves.

## A forced-oscillator estimate at a curvature zero

For a smooth periodic scalar \(k\) of period 1, put \(F=k''+k^3/2\).
For any \(c\ge0\), let \(R=\int_0^1(F-c\,{\rm sign}(k))^2\), with
\({\rm sign}(0)=0\). Set \(H=\max_{k=0}|k'|\), or zero when \(k\)
has no zero. With at most \(N\) sign changes there exists \(C_N\) such
that
\[
 H\le C_N(1+c^{2/3}+R^{2/5}).                                      \tag{1}
\]
Otherwise take a sequence along which the quotient tends to infinity.
Choose a zero realizing \(H\), and dilate arclength by \(a=\sqrt H\),
dividing curvature by \(a\). Now \(a\to\infty\), the period is \(a\),
and at the origin the new initial data are \((K,K')=(0,\pm1)\). Pass
to a subsequence fixing the sign. The equation becomes
\[
 K''+K^3/2=(c/a^3)\,{\rm sign}(K)+G,\qquad
 \int_{\mathbb R/(a\mathbb Z)}G^2=R/a^5 .
\]
Both \(c/a^3\) and \(R/a^5\) tend to zero. On any fixed bounded interval
the full forcing therefore tends to zero in \(L^1\). The unforced
solution satisfies \(K'^2+K^4/4=1\) and oscillates periodically between
\(\pm\sqrt2\). Indeed separation up to either simple turning point takes
finite time, and uniqueness gives the reflected half-periods. On a fixed
interval containing \(N+2\) alternating nonzero extrema of the unforced
solution, the forced solutions converge in \(C^1\). To verify this, stop
when their phase position first lies at distance one from the unforced
orbit. On this bounded phase neighborhood the vector field is Lipschitz,
and the integral equation and Gronwall bound this distance by a constant
times the \(L^1\) forcing, precluding the stop. The interval fits in one
period for all large indices. Its \(N+2\) alternating extrema then force
at least \(N+1\) genuine sign changes. This proves (1).

Here is an alternative with explicit constants and no limiting argument.
Put \(P=100(N+1)\). In the same normalized variables take the interval
\([0,P]\), assuming \(a\ge P\). Let \(f=K''+K^3/2\). If
\[
       Pc/a^3+\sqrt{P R/a^5}\le1/4,                                \tag{1a}
\]
then \(\int_0^P|f|\le1/4\). Write \(W=(K'^2+K^4/4)^{1/2}\).
As long as \(W>0\), \(W'=K'f/W\) and \(|W'|\le|f|\).
Starting from \(W(0)=1\), a first-hitting argument thus gives
\(3/4\le W\le5/4\), \(|K|\le2\), and \(|K'|\le2\) on the interval.
Integrating \((KK')'=W^2-3K^4/4+Kf\) gives
\[
 \tfrac34\int K^4 \ge \tfrac9{16}P-8-2\int|f|.
\]
The interval splits into at most \(N+1\) weakly single-sign subintervals
(zero plateaux may be attached on either side). On each, integrating
\(K''=f-K^3/2\) with its constant sign gives
\(\frac12\int |K|^3\le \int|f|+4\) there. Thus
\(\int K^4\le2\int |K|^3\le16(N+1)+4\int|f|\), contradicting the
preceding lower bound for \(P=100(N+1)\). Consequently either \(a<P\)
or (1a) fails. In particular
\[
 H\le \max\{P^2,(8Pc)^{2/3},(64P R)^{2/5}\}.
\]

## Dissipation on a unit-length slice

Put \(B=\int k^2\), \(D_1=\int F^2\), and now choose
\(c=B^{3/2}/2\). One-dimensional integration by parts gives
\[
 \int {\rm sign}(k)F=\tfrac12\int |k|^3
                   -2\sum_{z:k(z)=0,\ k'(z)\ne0}|k'(z)|
                 \ge c-2NH.                                        \tag{2}
\]
For the identity integrate on each positive and negative component.
The nonzero endpoint derivatives come precisely from the two adjacent
components at each simple zero. Tangential zeroes or zero intervals add
zero. The component integrals of \(k''\) converge absolutely since
\(\int |k''|<\infty\). Hölder on the unit circle gives \(\int|k|^3\ge
B^{3/2}\).

If \(D_1\ge c^2\) no negative deficit needs estimating. Otherwise (2)
and \(\int{\rm sign}^2(k)\le1\) imply
\[
 R\le D_1-2c(c-2NH)+c^2\le4cNH.
\]
Insert this into (1) to obtain
\(H\le C_N(1+B+B^{3/5}H^{2/5})\). Young's inequality absorbs the last
term at the cost of \(C_N B\), so \(H\le C_N(1+B)\). By (2) and
Cauchy–Schwarz,
\[
 \sqrt{D_1}\ge B^{3/2}/2-C_N(1+B).                                 \tag{3}
\]
The inequality holds in both cases.

For the original slice, \(B=2EL=2U\) and \(D_1=L^5D\).
Equation (3) implies, for \(U\) above an \(N\)-dependent threshold,
\[
 \frac{DL^2}{E^3}\ge 2(1-C_N/\sqrt U)^2.                            \tag{4}
\]
The threshold is chosen so the bracket is positive. On bounded \(U\),
the virial \(DL^3/E^2\ge4\pi^2\) gives \(DL^2/E^3\ge4\pi^2/U\).
Together these show that \(DL^2/E^3\ge d_N>0\) on every slice with
at most \(N\) changes of sign.

## The time estimate

Write \(\xi=\log(E(t_0)/E(t))\) after the stated starting time. Since
\(E'=-D<0\), this is a valid clock. The length variation
\(L'=\int kF\le\sqrt{2ED}\) gives
\[
 \frac{d\log U}{d\xi}\le \sqrt{\frac{2E^3}{DL^2}}-1 .
\]
When \(U\) exceeds a fixed large \(N\)-dependent threshold, (4) bounds
the right-hand side by \(C_N/\sqrt U\), so \(d\sqrt U/d\xi\le C_N\).
Integrating from the last threshold crossing, or from the initial time
when the entire interval lies above the threshold, yields
\(\sqrt U(t)\le C_{\gamma,N}(1+\xi(t))\).

The physical secant estimate follows by integrating \(|L'|\le\sqrt{2ED}\)
and using \((E^2)'=-2ED\):
\[
 (L(t)-L(s))^2\le (t-s)(E(s)^2-E(t)^2).                             \tag{5}
\]
In particular \(L(t)\le C_\gamma\sqrt{1+t}\), and Fenchel and
Cauchy–Schwarz give \(EL\ge2\pi^2\). Consequently
\(\xi(t)\le C_\gamma+\frac12\log(1+t)\).
If \(L(t)>2L(t_0)\), let \(s\) be the last time after \(t_0\) with
\(L(s)=L(t)/2\). Equation (5) gives \(L(t)^4\le16(t-s)U(s)^2\).
Combining these estimates proves the stated length bound. The remaining
times satisfy \(L(t)\le2L(t_0)\).

The coarser power estimate also follows directly. Set
\(m=\min(1,\sqrt{d_N/2})\); then \(EL^m\) is nonincreasing because
\(mE L'/L\le D\). At the same last doubling, (5) gives
\(L(t)^{2+2m}\le 4^{1+m}(t-s)\sup_{r\ge t_0}(E(r)L(r)^m)^2\).
This proves the exact exponent \(1/(2+2m)\) without an epsilon loss.
The positive limiting energy case is impossible under the hypothesis:
\(\xi\) bounded would bound \(U\) and \(L\), contradicting the virial
lower bound for \(D\) and finite total dissipation.

The bounded number of changes can fail in a hypothetical unbounded
general trajectory. This result imposes no Sturm monotonicity on the
fourth-order flow and gives no unconditional bound on that number.

## The finite-partition proof used for the formal verification

Write \(m=N+1,\ P=100m,\ Q=256Pm\). On the unit period choose \(z\)
maximizing \(k'^2+k^4/4\), set \(a^4=k'(z)^2+k(z)^4/4\), and let
\(J=\int |F|\). Every derivative has magnitude at most \(a^2\).
Splitting the whole period into at most \(m\) weakly one-sign pieces
and integrating \(k''=F-k^3/2\) gives
\[
 c=\tfrac12 B^{3/2}\le \tfrac12\int |k|^3\le J+2ma^2,\qquad
 J\le\sqrt{D_1}.
\]
When \(c>\sqrt{D_1}\), the nonnegative continuous error magnitude satisfies
\[
 R_0=\int(|F|-c)^2=D_1-2cJ+c^2\le4cma^2.
\]
For \(a>P\), apply the window calculation starting at this maximum to
\(K(y)=k(z+y/a)/a\). Its initial stress amplitude is one at any
initial phase. The estimate using \((KK')'\) allowed both endpoint
products to have magnitude four. Therefore the same window lower bound
holds at this initial phase. The window of unscaled length \(l=P/a<1\)
also has at most \(m\) one-sign pieces. After rescaling the result is
\[
 a^2/4<\int_z^{z+l}|F|\le cl+\sqrt{lR_0}.
\]
The upper bound uses periodicity to bound the shorter interval's squared
error by \(R_0\). These inequalities imply \(a^3<Qc\). Indeed
\(a^3\ge256Pmc\) would bound the two terms by \(a^2/256\) and
\(a^2/8\), respectively. Since \(Q\ge1\), \(a^3<QB^{3/2}/2\)
implies \(a\le Q\sqrt B\). Including \(a\le P\) gives
\(a^2\le P^2+Q^2B\). Consequently (3) holds with the explicit
\(C_N=2m(P^2+Q^2)\). This argument uses weak signs on whole subintervals
and needs no regularity of the zero set.
