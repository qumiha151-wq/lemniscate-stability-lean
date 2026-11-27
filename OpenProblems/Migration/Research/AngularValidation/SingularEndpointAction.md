# The singular migration action in every direction

Let \(X(t,u)\) be a smooth regular closed free elastic flow in the normal gauge, \(X_t=-FN\), \(F=k_{ss}+k^3/2\), on a compact time interval contained in its smooth time domain. For a fixed unit normal \(e\), put \(h=X\cdot e,\ x=X\cdot(-Je),\ z=x_s,\ Y=h_s,\ v=|X_u|\). Then \(T=(z,Y)\), \(N=(-Y,z)\) in the chosen frame, \(z^2+Y^2=1\). Fix a height \(\lambda\). Define \(M_\delta=\int(h-\lambda)\sqrt{x_u^2+\delta^2v^2}\,du\) for \(\delta\ge0\) and let \(Q_\delta\) for \(\delta>0\) denote the true instantaneous force expression in the [projected-height formula](../ProjectedHeight/ClosedProjectedHeight.md).

## Endpoint action and its kernel verification

For every fixed direction and \(t_0\le t_1\),
\[
 \left|\int_{t_0}^{t_1}Q_\delta\,dt-
                [M_0(t_1)-M_0(t_0)]\right|
 \le\delta\sum_{i=0}^1\int_{X(t_i)}|h-\lambda|\,ds .
\]
This follows from the exact two-time equality for \(M_\delta\) and \(0\le\sqrt{z^2+\delta^2}-|z|\le\delta\). In particular the integrated action has a right limit at zero, for every direction including degenerate ones. Under whole separation \(h_0\le\lambda-g_0,\ h_1\ge\lambda+g_1\), \(g_i\ge0\), this limit obeys
\[
 M_0(t_1)-M_0(t_0)\ \ge\
 g_0\oint_{X(t_0)}|dx|+g_1\oint_{X(t_1)}|dx|
 +\sum_{i=0}^1\max\{|A_i|,8/(3E_i^2)\}.
\]
Indeed \(B_{\delta,i}\ge\oint|dx|\) and the [two endpoint energy terms](TrueEndpointTransit.md) are uniform in \(\delta\). The quantitative time-integral estimate, the limit and the displayed lower bound have [Lean proofs](../../Migration/SingularEndpointAction.lean).

## A classical rate for every direction

The following are written arguments. In a fixed material chart the unsubstituted differential of \(M_0\) is the ordinary integral
\[
 Q_0=\oint\left[-F z|z|+
   (h-\lambda)\operatorname{sgn}(z)(F_sY+Fkz)\right]ds,
 \qquad \operatorname{sgn}(0)=0.                                      \tag{1}
\]
It exists at every smooth time and \(M_0'=Q_0\). To see this, observe \(h_t=-Fz,\ x_t=FY\). At a nonisolated zero of the smooth spatial function \(z\), every spatial derivative of \(z\) vanishes: a first nonzero Taylor coefficient would make that zero isolated. Since \(Y=\pm1\) there and \(z_s=-kY,\ Y_s=kz\), the curvature and its spatial derivatives also vanish there. In particular \((x_t)_u=v(F_sY+Fkz)=0\). At such a label the absolute value \(|x_u|\) is differentiable in time with derivative zero. At all labels where \(z\ne0\) its derivative is \(\operatorname{sgn}(z)(x_t)_u\). The isolated zeros at the chosen time are countable. Smoothness provides a uniform local bound on difference quotients, hence dominated convergence gives (1).

The vanishing of the force and its first derivative at accumulating tangencies has a [Lean proof](../../Migration/FlatProjectionZeros.lean) by successive applications of Rolle's theorem. The function \(Q_0\) is jointly continuous in time and direction, and \(Q_\delta\to Q_0\) uniformly on the compact time interval times the direction circle. For \(\delta>0\) differentiate the material integral to obtain
\[
 Q_\delta=\int h_t\sqrt{x_u^2+\delta^2v^2}
  +(h-\lambda)\frac{x_u(x_t)_u+\delta^2 vv_t}{\sqrt{x_u^2+\delta^2v^2}}\,du .
\]
For an arbitrary converging sequence of direction-time pairs with \(\delta\downarrow0\), fix its limit pair. At all its nonzero-projection labels, convergence of the integrand is immediate. At a nonisolated zero, \((x_t)_u=0\) at the limit pair, \(|x_u|/\sqrt{x_u^2+\delta^2v^2}\le1\), and \(\delta^2v/\sqrt{x_u^2+\delta^2v^2}\le\delta\). The integrand again converges there. The limit pair has at most countably many remaining labels. Smoothness and compactness give an integrable majorant for all the pairs. The same reasoning for \(\delta=0\) proves continuity of \(Q_0\), and compactness gives uniform convergence for positive \(\delta\). These statements refer to the integrated instantaneous force scalar over the spatial curve; no uniform convergence of the spatial force density at a tangency is needed.

## Simple and cubic tangencies

In particular every direction, at every smooth time, admits the absolutely convergent identity
\[
 Q_0=-\oint F\operatorname{sgn}(z)\,ds
    +2\sum_{\substack{z=0\\z_s\ne0}}
       (h-\lambda)\operatorname{sgn}(k) F
    +2\sum_{\substack{z=z_s=z_{ss}=0\\z_{sss}\ne0}}
       (h-\lambda)|F|.                                                \tag{2}
\]
Both sums count parameter labels. For the convergence check at an arbitrary time, the Frenet equations yield
\[
 z_{sss}=Yk^3-3zkk_s-Yk_{ss},\qquad
 YF=\tfrac32Yk^3-z_{sss}\quad\text{where }z=0 .
\]
At these labels \(|k|=|z_s|\). Take any finite set of distinct zero labels in cyclic order on the arclength circle. Extend them periodically to the line. Three applications of Rolle on the interval from the \(j\)-th through the \((j+3)\)-rd zero give a point there where \(z_{sss}=0\). Summing the fundamental-theorem bounds gives \(\sum_j|z_{sss}(s_j)|\le3\oint|z_{ssss}|\,ds\). One application on each adjacent pair similarly gives \(\sum_j|z_s(s_j)|\le\oint|z_{ss}|\,ds\). The periodic extension also treats lists with only one, two or three labels. Taking the supremum over finite subsets proves
\[
 \sum_{z=0}|F|\le 3\oint|z_{ssss}|\,ds+
      \tfrac32\|z_s\|_\infty^2\oint|z_{ss}|\,ds .
\]
The right side is uniformly bounded in direction and on compact smooth time intervals. The Frenet third derivative and the scalar simple and cubic coefficients have [Lean proofs](../../Migration/CubicTangencyFlux.lean).

Integrate the second term of (1) by parts on the components of \(\{z\ne0\}\). The ordinary bulk terms combine to \(-F\operatorname{sgn}(z)\) because \(z^2+Y^2=1\). The endpoint terms are absolutely summable by the preceding estimate. At an isolated zero their net coefficient is the negative jump of \(\operatorname{sgn}(z)\) times \((h-\lambda)FY\). At a simple zero \(z_s=-Yk\), giving the first sum in (2). At a cubic zero \(z_{sss}=-YF\), giving the second. Even-order zeros have no sign jump. All higher-order or flat zeros have \(F=0\) if sign-changing. Nonisolated endpoints also have \(F=0\). This proves (2) without a regular-direction hypothesis.

The signed tip sum in (2), integrated over the time window, must therefore pay at least the stated endpoint cost minus
\[
 \sqrt{(E_0-E_1)\int_{t_0}^{t_1}
     \left[L-\frac{(\oint|z|\,ds)^2}{\oint z^2\,ds}\right]\,dt}.
\]
Use the translation identity \(\oint Fz\,ds=0\) to subtract the least-squares projection of \(\operatorname{sgn}(z)\) on \(z\) from the bulk integrand, and apply Cauchy–Schwarz and \(E_0-E_1=\int\!\oint F^2\). The exact first term in that squared norm is the length of \(\{z\ne0\}\), bounded by \(L\) even in the presence of straight vertical pieces. The denominator is positive because a regular closed plane curve cannot be contained in a straight line. The necessary signed cost can be supplied by the evolution; these bounds do not establish non-migration in general.
