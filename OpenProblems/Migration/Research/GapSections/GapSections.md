# An energy bound for every horizontal section of a migrating elastic flow

Let \(X:S^1\times[0,T]\to\mathbb R^2\) be a smooth family of closed regular immersions. Use orthonormal coordinates \((x,h)\). Suppose \(h(X(u,0))\ge a>b\ge h(X(u,T))\) at every label. Let \(K\) be the image of the entire cylinder and suppose every slice has bending energy \(E(t)=\tfrac12\int k^2\,ds\le E_*\). For the free elastic flow take \(E_*=E(0)>0\).

**Theorem.** Every horizontal section \(K\cap\{h=c\}\), \(b<c<a\), contains a closed interval of length at least \(C/E_*\), where
\[
 G(v)=\int_0^v\sqrt{\sin q}\,dq,\quad H=G(\pi/2),\quad
 G(v_0)=H/\sqrt2,\qquad
 C=8\left(G(v_0)\sqrt{\sin v_0}-1+\cos v_0\right).
\]
Numerically \(C\simeq1.34156\). The exact expression follows from the proof. No optimality is claimed. No bound on length, turning number, material compression, or size of the gap enters this statement.

### Shallow arcs are transverse to vertical lines

On a slice with arclength parameter write \(m=\min h\), let \(T\) denote the unit tangent, and let \(\alpha=\arcsin |T_h|\in[0,\pi/2]\) be the distance of its tangent angle from the horizontal directions. If \(q\) is any point with \(T_h\ne0\), travel in the direction of decreasing height to the first horizontal tangent. This tangent exists by closedness, since the periodic derivative \(T_h\) has mean zero. On the resulting arc \(J\) the height is monotone. The distance to the set of horizontal angles is 1-Lipschitz in the tangent angle. Thus \(G(\alpha)\) is absolutely continuous in arclength, and its derivative has absolute value at most \(|k|\sqrt{|T_h|}\) almost everywhere. Cauchy–Schwarz gives
\[
 G(\alpha(q))^2\le\left(\int_J k^2\,ds\right)
                         \left(\int_J |T_h|\,ds\right)
      \le \left(\int_J k^2\,ds\right)(h(q)-m).
\]
The inequality holds trivially at a horizontal tangent. In particular \(T_x\ne0\) throughout \(h-m<\delta_*=H^2/(2E_*)\). An extremum of the horizontal coordinate has a vertical tangent, so every slice has vertical width at least \(\delta_*\). This last fact also covers arbitrarily small migration gaps.

### The first cap sweeps a full interval

Fix \(b<c<a\) and \(0<\delta<\delta_*\). Initially \(\min h>c\). At the terminal time \(\min h\le b-\delta_*<c-\delta\). Continuity of the minimum on the compact parameter circle gives a first time \(\tau\in(0,T)\) with \(\min h=c-\delta\). Throughout \(0\le t\le\tau\), every label at height at most \(c\) has \(T_x\ne0\), since its height is at most \(\delta\) above the minimum.

At time \(\tau\) fix a minimizer and take the connected component of \(\{h<c\}\) containing it. Its closure is a proper arc whose endpoints both have height \(c\). Indeed the slice width is at least \(\delta_*>\delta\), so a nonempty open complement has height strictly above \(c\). On the arc \(T_x\) has constant nonzero sign, so horizontal projection maps it homeomorphically onto a closed interval \(I_\delta\).

Take any interior \(x_0\in I_\delta\). The compact set of times in \([0,\tau]\) when some point of horizontal coordinate \(x_0\) has height at most \(c\) contains \(\tau\) and excludes zero. At its smallest time choose such a preimage. If its height were strictly below \(c\), transversality \(x_u\ne0\) and the implicit function theorem applied to \(x(u,t)=x_0\) would produce earlier preimages still strictly below \(c\). Hence \((x_0,c)\in K\). This also holds for the endpoints, taking their cap endpoints at \(\tau\). Thus \(I_\delta\times\{c\}\subset K\).

### Length of the projected cap

Split the cap at the minimizing label into its two arms, and set \(Q_i=\int_{\mathrm{arm}_i} k^2\,ds\). Both \(Q_i\) are positive since both arms start horizontally and rise by \(\delta>0\), and \(Q_1+Q_2\le2E_*\). On either arm the descending arc used above never leaves that arm before it reaches a horizontal tangent. It cannot leave through the height-\(c\) endpoint, and the minimizer is itself horizontal. For height \(y=h-m>0\) this gives
\[
 |dx|\ \ge\ f_y(Q_i)|dh|,\qquad f_y(Q)=\cot\bigl(G^{-1}(\sqrt{Qy})\bigr).
\]
At a horizontal tangent the right side vanishes when \(y>0\). For \(0<y\le\delta\) all indicated arguments satisfy \(Q_i y<H^2\). Integrating on the arm dominates \(\int_0^\delta f_y(Q_i)\,dy\), even if the height oscillates on the way. For instance first replace \(f_y\) by its truncation at a constant and use the fundamental theorem on the primitive of the truncated integrand, then let the truncation increase.

For fixed \(y\), \(f_y\) is decreasing and convex in \(Q\) on \(0<Q<H^2/y\). Indeed
\[
 \frac{d}{du}\cot(G^{-1}(u))=-(\sin(G^{-1}(u)))^{-5/2}
\]
is increasing. The outer function is decreasing convex and \(Q\mapsto\sqrt{Qy}\) is concave. The two arms have disjoint interiors and each is strictly monotone in horizontal projection. Jensen's inequality now gives
\[
 |I_\delta|\ge\int_0^\delta(f_y(Q_1)+f_y(Q_2))\,dy
           \ge2\int_0^\delta f_y(E_*)\,dy.
\]
For \(\delta\uparrow\delta_*\) choose a subsequence along which both interval endpoints converge. The horizontal slice of \(K\) is closed and bounded, so the limiting interval is contained in it. Its length is at least \(2\int_0^{\delta_*} f_y(E_*)\,dy\). Substitute \(y=G(v)^2/E_*\) to obtain
\[
 \frac4{E_*}\int_0^{v_0} G(v)\frac{\cos v}{\sqrt{\sin v}}\,dv
 =\frac8{E_*}\left(G(v_0)\sqrt{\sin v_0}-\int_0^{v_0}\sin v\,dv\right)=\frac C{E_*}.
\]
The integral representation proves positivity and justifies the improper endpoint limit.

### Dissipation consequences for the actual flow

Write \(B=\{b<h<a\}\). Fubini gives \(|B\cap K|\ge C(a-b)/E(0)\). For a free elastic flow with \(N=JT\), \(X_t=-FN+\lambda T\), \(F=k_{ss}+k^3/2\), the signed spacetime Jacobian in coordinates \((u,t)\) is \(-|X_u|F\). At almost every point of \(B\), the sum of signed preimages is zero, by the boundary degree formula and the endpoint half-plane separation. Every regular point of \(B\cap K\) has a preimage and hence has one of each sign. The area formula yields
\[
 \int_{X^{-1}(B)}F_+\,ds\,dt
 =\int_{X^{-1}(B)}F_-\,ds\,dt
 \ge \frac{C(a-b)}{E(0)}.
\]
This also holds for any open substrip, replacing \(a-b\) by its width. On the two disjoint endpoint half-planes the absolute multiplicity is at least the absolute winding number of the corresponding endpoint. Adding, and applying the energy identity and Cauchy–Schwarz, gives
\[
 \|w_0\|_1+\|w_T\|_1+\frac{2C(a-b)}{E(0)}
 \le \sqrt{(E(0)-E(T))\int_0^T L(t)\,dt}.
\]
These restrictions concern any actual migrating flow. The available dissipation and time can exceed the lower bounds, so existence of a migrating flow remains undecided.

### Timing of the two outermost stationary contacts

For almost every oriented separating line, the leftmost and rightmost swept points on that line are reached at disjoint compact sets of times. In particular there is a strictly positive time gap between these two sets for that line. No uniform lower bound over lines is asserted.

Here almost every refers to angular measure times offset measure on oriented lines. At positive times the elastic force is spatially analytic in arclength and is nonzero somewhere on each slice by the dilation first variation. Thus its spatial zeros have finite order, including in any smooth regular material coordinate, since the arclength change is a local diffeomorphism. The spacetime zero set in the open time interval is covered by countably many smooth graphs \(u_j(t)\). Indeed, at a zero of order \(m\), the equation \(\partial_u^{m-1}F=0\) is locally a graph by the implicit function theorem. The order-\(m\) subset has a countable subcover by such neighborhoods, and \(m\) ranges over the positive integers. The graphs need only contain the zeros of that order.

Write \(P_j(t)=X(u_j(t),t)\). For each pair of graphs and times in their common domains with \(P_j(t)\ne P_k(t)\), the two oriented lines through both points depend smoothly on \(t\), since their unit normals are \(\pm J(P_j-P_k)/|P_j-P_k|\). Their images in the two-dimensional space of lines have measure zero by the area formula in local charts. The countable union of these exceptions still has measure zero. Thus for every remaining line, there are never two distinct physical force-zero points on that line at the same interior time.

If the line strictly separates the endpoint slices, its two horizontal trace extrema differ by at least \(C/E_*\). All their preimages occur at interior times and have Jacobian zero, since an invertible Jacobian would put an open neighborhood of the extremal point in the swept image. The physical force vanishes at each preimage. For the nonexceptional lines the two nonempty sets of preimage times are disjoint. Both are compact by compactness of the parameter-time cylinder, so their distance is positive. This conclusion allows self-intersections and coincident material labels. The exceptional set is measured over directions and offsets jointly, and a given fixed direction can be exceptional. The positive-time analyticity and the signed area formulas used above are proved in [Swept critical values](../SimilarityReturns/SweptCriticalValues.md).

### Machine-checked scope

Within the independent Migration project, \(\texttt{GapCapSweep.lean}\) proves the vertical-line hitting theorem from the actual smooth periodic immersion and its horizontal derivative, the inclusion of the entire projected cap in the swept section, compactness of the physical trace, and the area lower bound from a family of such caps. It uses the inverse function theorem and disintegration of product measure without selecting measurable cap endpoints. The curvature inequality, the construction of the first cap for the prescribed energy threshold, the constant \(C\), and the force and timing conclusions are proved in this note. For applying the formal area estimate to the limiting cap width, first use any \(W<C/E_*\) and then increase \(W\) to the limit. The argument with \(\delta\uparrow\delta_*\) supplies the slightly narrower genuine caps.
