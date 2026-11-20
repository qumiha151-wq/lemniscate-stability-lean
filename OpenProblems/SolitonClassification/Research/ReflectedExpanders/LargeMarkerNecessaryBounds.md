# Necessary quarter-length and nodal growth at large initial slope

Consider the reflected pure-expander shooting problem at dilation coefficient one. Start at \(X=0,\ k=0,\ k_s=b>0\) with \(T(0)=(1,0)\), and suppose a positive quarter time \(s_b\) satisfies \(k_s(s_b)=X(s_b)\cdot T(s_b)=0\). The following estimates apply along any sequence of such solutions with \(b\to\infty\).

Let \(U\) solve \(U''=-U^3/2,\ U(0)=0,\ U'(0)=1\), with least period \(P\), and set
\[
 \gamma=\frac1P\int_0^P U^2/2\,dx,\qquad \tau_*=\sqrt{3/\gamma}.
\]
Then
\[
 \liminf_{b\to\infty}\frac{s_b}{\sqrt b}\ \ge\ \tau_*,
 \qquad
 \liminf_{b\to\infty}\frac{\#\{s\in(0,s_b):k(s)=0\}}{b}
 \ \ge\ \frac{\pi\tau_*}{2P}.
\]
The two estimates are necessary conditions. Their proof controls the evolution up to every fixed slow time strictly less than \(\tau_*\).

## Averaging before the stress vanishes

Put \(\delta=1/b,\ x=\sqrt b\,s,\ \tau=\delta x,\ K=k/\sqrt b,\ V=k_s/b,\ Z=X/\sqrt b\), and let \(W=(K^2/2)T+VN\). The exact arclength equations give
\[
 K_x=V,\quad V_x=-K^3/2-\delta Z\cdot N,\quad
 Z_\tau=T,\qquad W_\tau=-(Z\cdot N)N .
\]
Initially \(Z=0\) and \(W=e_0=(0,1)\). Write \(A=|W|\) and \(e=W/A\). As long as \(A>0\), the smooth phase \(\phi\in\mathbb R/P\mathbb Z\) is defined by
\[
 K=\sqrt A\,U(\phi),\qquad V=A\,U'(\phi).
\]
Indeed the unit level \(v^2+k^4/4=1\) is a smooth embedded periodic orbit with nonvanishing tangent \((v,-k^3/2)\), and radial scaling by \(A\) identifies all its positive levels. Lift the phase with \(\phi(0)=0\). Write \(u=U^2/2,\ w=U'\). The frame has the exact expressions \(T=u e-w Je,\ N=w e+u Je\). With \(A\) bounded away from zero and the slow variables in a compact set, the phase satisfies
\[
 \phi_\tau=\sqrt A/\delta+O(1).
\]
This follows by applying the smooth phase differential to \((K_x,V_x)\). Its unperturbed term is \(\sqrt A\), and its error is bounded by \(C\delta |Z|\). The estimates hold also at turning points of \(K\).

Use angle brackets for the period average in \(\phi\). Direct integration gives \(\langle w\rangle=\langle wu\rangle=0\) and \(\langle u\rangle=\gamma>0\). Multiplying the \(U\) equation by \(U\) and integrating yields \(\langle w^2\rangle=\langle U^4/2\rangle=2\langle u^2\rangle\); the energy identity \(u^2+w^2=1\) therefore gives \(\langle w^2\rangle=2/3,\ \langle u^2\rangle=1/3\). Consequently the equation for averaged slow variables is
\[
 \overline Z_\tau=\gamma e,\qquad
 \overline W_\tau=-\tfrac23(\overline Z\cdot e)e
                   -\tfrac13(\overline Z\cdot Je)Je,\qquad
 e=\overline W/|\overline W|.
\]
In particular the average of the mixed term is computed with its actual phase distribution. Starting from the specified data its unique solution before \(\tau_*\) is
\[
 \overline Z=\gamma\tau e_0,\qquad
 \overline W=(1-\gamma\tau^2/3)e_0 .
\]

For a quantitative error bound fix \(0<B<\tau_*\) and a compact neighborhood of this trajectory disjoint from \(W=0\). Denote the slow variables by \(Y=(Z,W)\) and their exact velocity by \(f(Y,\phi)\). The smooth difference \(f-\bar f\) has zero phase mean at each \(Y\), so there exists a smooth \(P\)-periodic \(D(Y,\phi)\) with \(D_\phi=(f-\bar f)/\sqrt{|W|}\). Along the exact solution,
\[
 f(Y,\phi)-\bar f(Y)=\delta\,\frac{dD}{d\tau}+O(\delta),
\]
uniformly on this neighborhood. The chain rule here uses bounded \(f,D_Y,D_\phi\) and the bounded phase-speed error. Integrating and applying Gronwall gives \(Y-\overline Y=O_B(\delta)\) on \([0,B]\), first up to exit, and then on the full interval by continuation. The variables \(K,V\) remain bounded there because \(W\) does, and the smooth reconstruction excludes finite-time loss of existence on the interval.

## The first seam and the number of zeros

In this region \(e=e_0+O_B(\delta)\). At \(V=0\), the energy identity and \(u\ge0\) give \(T=e\). Hence at such a point
\[
 Z\cdot T=\gamma\tau+O_B(\delta).
\]
If a sequence of seams occurred with \(\tau\le B\), their fast times \(x=\tau/\delta\) would be bounded. On every fixed fast interval the original scaled equations also give convergence to the unperturbed oscillator. In the fast position coordinates \(Y_0=Z/\delta=\sqrt b\,X\) this follows directly from \(Y_{0,x}=T,\ V_x=-K^3/2-\delta^2Y_0\cdot N\). At the limit \(T=(U',U^2/2)\), so
\[
 Y_0(x)=\bigl(U(x),\ \int_0^x U^2/2\bigr).
\]
At every positive limiting point with \(U'=0\), the tangent is vertical and \(Y_0\cdot T=\int_0^x U^2/2>0\). A zero limiting time is excluded by \(U'(0)=1\). This contradicts the seam condition. Thus for every fixed \(B<\tau_*\) all sufficiently large shooting roots have \(\tau_b>B\), proving the length estimate.

Finally the phase is strictly increasing on \([0,B]\) for small \(\delta\), and
\[
 \delta\phi(B)=\int_0^B\sqrt{1-\tau^2/\tau_*^2}\,d\tau+O_B(\delta).
\]
There are two simple zeros per period of \(U\). Counting up to \(B\) gives the stated lower bound after \(B\uparrow\tau_*\), since the integral then equals \(\pi\tau_*/4\). At \(\tau_*\) the averaged stress reaches zero and the phase coordinate degenerates. A continuation of its phase through that point, needed for a phase-matching existence argument, does not follow from these estimates.
