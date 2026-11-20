# A common disk for all closed free elastic flows on a universal short time scale

Let \(X\) be a smooth closed immersed free elastic flow with velocity
\(-FN\), energy \(E=\frac12\int k^2ds\) and dissipation \(D=\int F^2ds\).
For \(s\) in its smooth lifetime write \(E_s=E(s)>0\) and
\(K_t=\operatorname{conv}X(t)\).

**Theorem.** There is a point \(p\in K_s\), determined by the initial
slice alone, for which
\[
 \overline B\bigl(p,(6E_s)^{-1}\bigr)\subseteq K_t
 \quad\text{whenever}\quad
 0\le (t-s)E_s^4<\frac{1}{36(\sqrt2+\pi\sqrt6)^2}.
\]
This applies to every turning number and every initial value of \(E_sL_s\).

For any unit vector \(e\), write \(H_t(e)=\max X(t)\cdot e\) and
\(W_t(e)=H_t(e)+H_t(-e)\). The static strip estimate
\(E_sW_s(e)\ge2\) follows by a rotation from the project’s
position-defined vertical estimate. Here is the construction of \(p\).
Take a diameter \(AB\) of the initial curve, and let \(C\) be a curve
point farthest from its line. The altitude of \(ABC\) is at least half
the width in the direction perpendicular to \(AB\), hence at least
\(1/E_s\). Since each side is at most \(|AB|\), the inradius is
twice the area divided by the perimeter, at least \(1/(3E_s)\).
Take \(p\) to be the incenter. In particular,
\(H_s(e)\ge e\cdot p+1/(3E_s)\) simultaneously for all \(e\).

The support function obeys the following one-sided estimate for
\(0<d\le2/E_s\):
\[
 H_t(e)\le H_s(e)-d
 \quad\Longrightarrow\quad
 \sqrt{(t-s)E_s}\ \ge\
 \frac{d}{\sqrt{2E_s}+\pi/\sqrt d}.
\tag{1}
\]
To see this, put \(h_0=H_s(e)-d\). Choose \(\chi(h)=0\) below \(h_0\),
\(\chi(h)=\sin^2(\pi(h-h_0)/(2d))\) on \([h_0,h_0+d]\), and
\(\chi(h)=1\) above \(h_0+d\). This \(C^1\) function satisfies
\(0\le\chi\le1\) and \(|\chi'|\le (\pi/d)\sqrt\chi\).
Because \(W_s(e)\ge d\), both arcs from a maximum point to a minimum
point traverse that entire height interval. Unit speed gives
\(\int\chi\,ds\ge\left|\int\chi(h)\,dh\right|\) on each arc,
so \(m(s):=\int_{X(s)}\chi(X\cdot e)\,ds\ge d\). At the later time
\(m(t)=0\).

Along the actual flow, variation of the height and arclength gives
\[
 |m'(v)|\le
 \bigl(\sqrt{2E_s}+(\pi/d)\sqrt{m(v)}\bigr)\sqrt{D(v)} .
\]
Indeed \(\partial_t ds=kFds\), the height derivative is
\(-F N\cdot e\), and Cauchy–Schwarz gives this inequality using
\(\chi^2\le1\) and \(E(v)\le E_s\).
Apply the chain rule to
\(\Phi(y)=\int_0^y [\sqrt{2E_s}+(\pi/d)\sqrt u]^{-1}\,du\)
for \(y\ge0\), extending its derivative continuously to negative
arguments if needed. The integrand decreases, whence
\(\Phi(m(s))\ge\Phi(d)\ge d/(\sqrt{2E_s}+\pi/\sqrt d)\).
On the other hand \(\int_s^t\sqrt D\,dv\le
\sqrt{(t-s)(E_s-E(t))}\le\sqrt{(t-s)E_s}\). This proves (1).

Take \(d=1/(6E_s)\). At the times in the theorem, (1) yields
\(H_t(e)>H_s(e)-d\ge e\cdot p+1/(6E_s)\) for every unit \(e\).
The half-space characterization of a compact convex body yields the
asserted disk. The interval length is expressed in the physical
biharmonic time scale. A chain of such local disks does not by itself
produce a single center shared at arbitrarily separated times.

The static vertical width estimate and the cutoff mass variation use
the independent Migration project, in
[`StripCurvature.lean`](../../Migration/StripCurvature.lean),
[`LocalizedFirstVariation.lean`](../../Migration/LocalizedFirstVariation.lean),
and [`LocalizedRateBound.lean`](../../Migration/LocalizedRateBound.lean).
