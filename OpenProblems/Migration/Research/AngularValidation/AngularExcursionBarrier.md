# A sharp lower bound on the projected length of every closed curve

Write \(E=\tfrac12\oint k^2\,ds\) for the bending energy of a smooth regular immersed closed plane curve, \(T\) for its unit tangent, and \(m\in\mathbb Z\) for its turning number. For every unit vector \(e\),
\[
 E\oint|T\cdot e|\,ds\ \ge\ C_* \max(1,m^2),\qquad
 C_*=8\left(\int_0^{\pi/2}\sqrt{\cos z}\,dz\right)^2
       \simeq 11.4843201767.                                      \tag{1}
\]
The projected length counts all traversals. The universal coefficient is optimal, even among smooth strictly convex curves.

Choose the angle lift \(\theta\) from \(e\), \(T=(\cos\theta,\sin\theta)\) in the rotated frame. It has \(\theta_s=k\), \(\theta(L)-\theta(0)=2\pi m\). Let \(w(z)=\sqrt{|\cos z|}\), \(J=\int_0^{\pi/2}\sqrt{\cos z}\,dz\). The weight is \(\pi\)-periodic, with integral \(2J\) on each period. When \(m\ne0\), integrating \(\theta_s w(\theta)\) gives absolute value \(4J|m|\). When \(m=0\), the angular range has width at least \(\pi\). A shorter range would make the tangent component along its middle direction everywhere positive, contradicting closure. Both extreme angles occur. Any primitive of \(w\) composed with \(\theta\) has equal endpoint values and its total variation is at least twice the difference between its values at the extreme labels, irrespective of their order. Hence \(\int |k|w(\theta)\,ds\ge4J\) also for zero turning. Squaring and applying Cauchy–Schwarz gives (1).

To verify sharpness let a once-turning convex curve be parametrized by its tangent angle and prescribe \(k_\epsilon(\theta)=(\cos^2\theta+\epsilon^2)^{1/4}\), for \(\epsilon>0\). Integrate \(X_\theta=(\cos\theta,\sin\theta)/k_\epsilon\). The half-period reverses the vector, so the curve closes exactly. Its positive curvature and single full turn give a strictly convex curve. Now \(E=\tfrac12\int_0^{2\pi} k_\epsilon\,d\theta\to2J\) and \(\oint |T\cdot e|ds=\int_0^{2\pi}|\cos\theta|/k_\epsilon\,d\theta\to4J\), by dominated convergence with \(e=(1,0)\). The product tends to \(C_*\). Covers give the same optimal constant with the \(m^2\) factor for each nonzero \(m\).

## A necessary cost for whole-curve migration

In the [two-time projected-height identity](../OrientedAreaTransit/OrientedAreaTransit.md), use \(e\) parallel to the proposed separating line. Write \(E_i,A_i\) for the energy and signed area at the two times and \(g_i\ge0\) for their height gaps from the line. The regularized projected length \(B_{\delta,i}=\oint\sqrt{(T\cdot e)^2+\delta^2}\,ds\) dominates the projected length in (1). Consequently the actual integral of the regularized height evolution between these times is at least
\[
      C_*\max(1,m^2)(g_0/E_0+g_1/E_1)+|A_0|+|A_1|.             \tag{2}
\]
The energies are positive because the curves close and are regular. For given endpoint shapes the original projected-length terms can provide stronger bounds. Formula (2) needs only the turning number, energy, height gap and area of each endpoint. In the written absolute-winding refinement of the same identity the two absolute oriented areas can again be replaced by the corresponding integrals of absolute winding.

### A positive cost even for vanishing endpoint gaps and signed areas

Let \(W=\max h-\min h\) on one endpoint curve, and let \(a\) be any level below that curve. Then
\[
 \oint (h-a)|dx|\ \ge\ \frac{2W}{E}-\frac{4}{3E^2}\ \ge\ \frac{8}{3E^2}. \tag{2a}
\]
The same holds with \(a-h\) for a level above the curve. Indeed \(EW\ge 2\) by the strip-curvature theorem [already verified for closed slices](../../Migration/StripCurvature.lean). At a highest point use periodic arclength with origin there and let \(T_0\) be its horizontal unit tangent. For \(0\le r\le 2/E\), the two arcs of length \(r\) drawn from this point are disjoint up to endpoints: the closed-curve Fenchel inequality and Cauchy–Schwarz give \(EL\ge 2\pi^2>4\). At their endpoints the heights exceed \(a+W-r\) in the weak sense, by unit speed. Also
\[
 |x_s(r)|+|x_s(-r)|\ \ge\
 T_0\cdot T(r)+T_0\cdot T(-r)
 =2-\tfrac12\big(|T(r)-T_0|^2+|T(-r)-T_0|^2\big)
 \ge 2-rE .
\]
The last inequality follows from the fundamental theorem of calculus applied to \(T_s=kN\), Cauchy–Schwarz on each arc, and the *sum* of the two disjoint curvature budgets. Since both \(W-r\) and \(2-rE\) are nonnegative, integrating \((W-r)(2-rE)\) from 0 to \(2/E\) gives (2a). Reflection proves the other sign.

Consequently in (2) each \(|A_i|\) may be replaced by
\[
       \max\!\left\{|A_i|,\;2W_i/E_i-4/(3E_i^2)\right\}.
\]
To check additivity, put \(a=\lambda+g_1\) at the upper endpoint and \(a=\lambda-g_0\) at the lower. The constant gap contributions give \(g_i B_{\delta,i}\); the remaining terms dominate both \(|A_i|\) and the corresponding absolute height moment in (2a). The estimate therefore forces a strictly positive contribution from each endpoint even if the trace has cancelling oriented lobes and both chosen gaps tend to zero. This argument and the sharpness construction above are written proofs.

## Barrier to obtaining an example by flattening a periodic curve

Take a translation-periodic unit-speed curve with period vector \(D\), \(d=|D|\), and zero turning per period. For any lift \(\phi\) of its tangent angle relative to a chosen axis, let \([\alpha,\beta]\) be its range. For every \(q\) such that \(\cos\phi+q\ge0\),
\[
 E(d+Lq)\ \ge\
       2\left(\int_{\alpha}^{\beta}\sqrt{\cos z+q}\,dz\right)^2. \tag{3}
\]
Indeed \(\phi(L)=\phi(0)\) gives a full two-way traversal of the primitive of the weight, and \(\int(\cos\phi+q)ds\le d+Lq\). Cauchy–Schwarz proves (3).

Suppose a smooth elastic-flow orbit starts with tangent image contained in no closed semicircle and later has its entire tangent image in some open semicircle. The latter condition includes a regular graph after rotation. Turning zero is necessary for the final condition. A continuous angle lift on the space-time parameter strip has equal endpoint values on each slice. Its maximum and minimum over one period vary continuously; their difference passes through \(\pi\), since every connected angular lift with width at most \(\pi\) lies in a closed semicircle, and the final lift has width less than \(\pi\). On a critical slice choose the middle tangent direction, so \(\alpha=-\pi/2,\beta=\pi/2,q=0\). Then (3) gives \(Ed\ge C_*\). The translation vector is conserved by the periodic evolution, and bending energy per period decreases by the usual periodic energy identity. In particular \(E_{\rm initial}d\ge C_*\). A family with bounded initial energy and \(d\to0\) cannot achieve migration by this transition.

The critical-slice constant is sharp. Solve the smooth pendulum system \(\phi'=k,\ k'=-\tfrac12\sin\phi\) through \((\phi,k)=(0,1)\). Its first integral is \(k^2=\cos\phi\). It traverses the angles between \(-\pi/2\) and \(\pi/2\) and returns; the travel times are finite since \((\cos\phi)^{-1/2}\) is integrable at the ends. Integrating its tangent over one period gives horizontal displacement \(4J\) and zero vertical displacement by symmetry. The energy per period is \(2J\). Moreover \(k''=-k\cos\phi/2=-k^3/2\), so this is the stationary rectangular elastica. Attainment concerns (3) on a single slice; it does not provide an orbit which changes from an overhang to a graph at the same energy.

There is also an exactly closed consequence. If the range width \(A\) of a zero-turn closed curve is between \(\pi\) and \(2\pi\), centre the angle range and set \(q=-\cos(A/2)\). Closure replaces \(d\) by zero in (3). On \([-\pi/2,\pi/2]\) the integrand dominates \(\sqrt{\cos z}\), hence \(EL[-\cos(A/2)]\ge C_*\). Thus a finite-energy closed curve of given length must exceed a semicircle by a quantitative amount. Neither (1) nor (3) excludes separation while the curve continues to overhang.
