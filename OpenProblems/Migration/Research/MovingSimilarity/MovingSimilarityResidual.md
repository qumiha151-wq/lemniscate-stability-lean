# Support bounds in moving similarity coordinates

Let an immersed closed planar curve have normal velocity \(-FN\), with \(F=k_{ss}+k^3/2\) and \(E=\tfrac12\int k^2ds\). The following estimate applies to smooth flows on a compact time interval \([0,T]\). Choose any smooth family of direct similarities \(S_t(y)=b(t)+\rho(t)R(t)y\), with \(S_0\) the identity and \(\rho>0\). Put \(A=\dot\rho I/\rho+\dot R R^{-1}\), \(v=\dot b-Ab\) and
\[
 w=F+(AX+v)\cdot N,\qquad \Delta=\int w^2 ds,\qquad
 I=\int_0^T\frac{\sqrt{2E\Delta}}{\rho}\,dt,\quad
 B=\int_0^T\frac{\sqrt{\Delta}}{\rho^{3/2}}\,dt.
\]
Write \(Y_t=S_t^{-1}X_t\), \(L_*=L(T)/\rho(T)\), and \(h_Z(e)=\max_{z\in Z}e\cdot z\) for \(|e|=1\).

**Theorem.** For any \(d>0\), write \(m=\min(d,L_*/2)\). Then
\[
 I+(\pi/d)B\sqrt m<m\quad\Longrightarrow\quad
 h_{Y_T}(e)< h_{X_0}(e)+d\quad\text{for every unit }e.
\]
Equivalently the terminal convex hull lies inside the open \(d\)-neighbourhood of the initial convex hull in the moving coordinates. Reversing the time direction in these same coordinates gives the opposite support inequality, with \(m=\min(d,L(0)/2)\) and the same \(I,B\). The proof uses no sign of the normal velocity.

For a whole-curve migration certificate choose a direction \(e\) in physical coordinates. Suppose the predicted final curve \(S_T X_0\) satisfies \(h_{S_T X_0}(e)+\rho(T)d\le\min_{X_0}e\cdot X_0\). Under the strict budget above, \(h_{X_T}(e)<\min_{X_0}e\cdot X_0\), because the support transformation uses direction \(R(T)^{-1}e\). A fixed line then strictly separates the actual endpoint images. This is sufficient on one trajectory. Verifying these inequalities on an actual trajectory would still be needed to establish existence.

**Proof.** In the \(Y\) coordinates the normal velocity is \(V=-w/\rho\), arclength is \(ds_Y=ds/\rho\), curvature is \(k_Y=\rho k\), and therefore \(\int V^2ds_Y=\Delta/\rho^3\), \(E_Y=\rho E\). Fix \(e\), put \(H=h_{X_0}(e)\), and choose the nondecreasing height cutoff \(\chi(z)\) equal to zero for \(z\le H\), one for \(z\ge H+d\), and \(\sin^2(\pi(z-H)/(2d))\) in between. It is \(C^1\), takes values in \([0,1]\), and \(|\chi'|\le(\pi/d)\sqrt\chi\). Its arclength mass \(M(t)=\int\chi(e\cdot Y)ds_Y\) starts at zero. Arclength differentiation gives
\[
 M'=\int [\chi'(e\cdot N_Y)-k_Y\chi]V\,ds_Y,
 \qquad |M'|\le \bigl[(\pi/d)\sqrt M+\sqrt{2E_Y}\bigr]\sqrt{\int V^2ds_Y}.
\]
The terms from any tangential parametrization integrate to a periodic total derivative. If the terminal support is at least \(H+d\), take both arclength arcs of length \(m\) starting from a terminal support point. Their interiors are disjoint. At distance \(r\in[0,m]\) the height is at least \(H+d-r\) by unit speed. Thus \(M(T)\ge 2\int_0^m\cos^2(\pi r/(2d))dr\ge m\). The first time at which \(M=m\) obeys \(m\le I+(\pi/d)B\sqrt m\), which proves the theorem. Compactness of the unit circle gives a strict uniform support margin, establishing the convex-hull formulation.

## Testing the initial fitted centre on strictly convex data

For a regular closed noncircular curve define \(C_N,C_T\) as the minimizers of \(\int ((X-c)\cdot N)^2ds\) and \(\int((X-c)\cdot T)^2ds\). Put \(p=(X-C_N)\cdot N\), \(q=(X-C_T)\cdot T\), and let \(J\) denote positive quarter rotation. The full instantaneous similarity fit for the true free-elastic velocity has angular-to-dilation ratio and centre
\[
 u=-\frac{\int pq\,ds}{\int q^2ds},\qquad
 O=C_N+\frac{uJ(C_T-C_N)+u^2(C_T-C_N)}{1+u^2}.
\]
Indeed \(p,q\) are both orthogonal to the two translation normal modes. The actual stress identities give \(\int FN=0\), \(\int Fq=0\), \(\int Fp=-E\). Consequently the best approximation to \(-F\) by normal components of infinitesimal similarities is \(a(p+u q)\), with \(a=E/\int(p+u q)^2>0\). The formula for \(O\) follows from \((I+uJ)O=C_N+uJ C_T\). Also the best pure dilation and translation fit has centre \(C_N\), with positive rate \(E/\int p^2\).

There is a single smooth strictly convex curve on which both of these fitted centres lie outside its convex hull, beyond different sides. Start with the counterclockwise quadrilateral with successive vertices
\[
 (0,0),\quad (1,-P),\quad (2,Q-P),\quad (2,0),
 \qquad P=\frac{2r}{1-r^2},\quad Q=\frac{2s}{1-s^2},
 \qquad r=1/1001,\quad s=1/1201.
\]
Its edge lengths are \((1+r^2)/(1-r^2),(1+s^2)/(1-s^2),P-Q,2\). For an edge of length \(l\), midpoint \(m_0\), tangent \(t\) and normal \(n\), its normal matrix and right side are \(l nn^\top\) and \(l(m_0\cdot n)n\). The tangent centre uses \(t\) in both places. Write \(p_m=(m_0-C_N)\cdot n\), \(q_m=(m_0-C_T)\cdot t\). The edge integrals of \(pq,q^2\) are \(lp_mq_m\) and \(lq_m^2+l^3/12\). These formulas involve rational numbers only. The accompanying script checks the strict bounds
\[
 -72/10^5<(C_N)_y+P-Q((C_N)_x-1)<-71/10^5,\qquad
 25/10^5<O_y<26/10^5,\qquad -136/10^5<u<-135/10^5.
\]
The entire polygon has \(y+P-Q(x-1)\ge0\) and \(y\le0\).

To smooth with positive curvature, express the polygon by its periodic support function \(h(\theta)\). Its radius measure \(h+h''\) is the sum of edge lengths at their exterior normal directions. Convolve \(h\) on the circle with smooth nonnegative approximate identities and add positive constants tending to zero. The resulting radii are smooth positive functions, and their support curves are smooth, embedded, and strictly convex. The support functions converge uniformly. For completeness, use kernels supported in angles \(\eta\downarrow0\). On each interval of width \(2\eta\) around an edge normal the normal and tangent differ from their edge values by \(O(\eta)\), the arclength tends to the edge length, and the arc starts at a point tending to the first edge vertex. Integration of its unit tangent shows uniform convergence on that arc, in arclength, to the straight segment. On the remaining angles the total arclength tends to zero. Thus every position-tangent arclength integral used above converges to its polygon value. The Gram matrices are invertible at the polygon, and \(\int q^2>0\). The strict separations consequently persist after smoothing.

The size of the initial fitting error can also be determined. Use the same parameter \(\eta\) for the positive constant added to the support function and the angular smoothing width. The radius of curvature is at least \(\eta\) everywhere and equals \(\eta\) outside the four intervals around edge normals. On these circular arcs \(k=1/\eta\), \(F=k^3/2\). For small \(\eta\) they carry at least \(\pi\) in total turning, hence \(D=\int F^2ds\ge\pi/(4\eta^5)\), while \(E\le\pi/\eta\). The squared norm \(J_0=\int(p+u q)^2ds\) tends to a strictly positive polygon value. Indeed, if it vanished on the polygon then on each straight edge the constant \(p\) would equal \(-u q\), where \(q\) has unit arclength derivative. This forces \(u=0\), then every edge line would pass through the same point \(C_N\). The actual share of the initial squared normal velocity captured by the best similarity fit is \(E^2/(J_0D)=O(\eta^3)\). It tends to zero even though both fitted centres are strictly exterior. Thus the fitted direction alone fails to control the initial residual even in relative units. Applying the sufficient criterion requires the time integral along the evolving shape. [Free elastic flow and its open questions](https://arxiv.org/abs/2404.12619) · [Exact rational calculation](quadrilateral.py)

For the preceding example one can check the physical initial support motion as well. Choose an even smoothing kernel maximal at zero. At each of the four original edge normal directions the smoothed curvature radius has a local maximum, since the four translated kernel supports are disjoint. There \(k\) has a local minimum and \(F=k_{ss}+k^3/2>0\). For the counterclockwise curve \(-N\) is the exterior normal, so the actual support initially increases in all four such directions. This also holds for the two exterior normal directions of the separating edges found by the rational calculation.

## Polar angle and the turning of each curvature lobe

Let a nonstraight closed similarity profile have actual centre at the origin, dilation rate \(a>0\), rotation rate \(b\), radius \(r=|X|\), tangent \(T\), normal \(N=JT\), and stress \(W=(k^2/2)T+k_s N\). The profile obeys \(F=-aX\cdot N-bX\cdot T\). Suppose the centre is strictly outside the convex hull. There is then a smooth periodic branch \(\phi=\arg X\) whose oscillation is strictly less than \(\pi\). Write \(\psi=\phi-(b/a)\log r\). Differentiating radius and argument gives \(F=a r^2\psi_s\).

Where \(k\ne0\), put
\[
 B=\frac{k^2/2}{k_s^2+k^4/4},\qquad A=a r^2 B,
 \qquad \alpha=\arctan(2k_s/k^2).
\]
Then \(k+\alpha_s=BF=A\psi_s\). Indeed \(W_s=FN\) and \(W\cdot T=k^2/2\). The argument of \(W\) differs from a tangent-angle lift by \(\alpha\), and its derivative equals \(\det(W,W_s)/|W|^2=BF\).

The coordinate profile system is analytic in arclength, since the Frenet and force equations make \((X,T,k,k_s)\) solve an autonomous polynomial ODE. Curvature cannot vanish identically on a regular closed curve. Its zeros are isolated, with finitely many per period. At any order-\(j\) zero \(s_0\), setting \(u=s-s_0\) and \(k=u^j g(u)\), \(g(0)\ne0\), gives
\[
 B=\frac{u^2g^2}{2\big((jg+ug')^2+u^{2j+2}g^4/4\big)}.
\]
Thus \(B,A\) extend smoothly and vanish at each zero. On a lobe \(D\) between successive zeros, where \(\sigma=\operatorname{sign}k\), \(\alpha\) tends to \(\sigma\pi/2\) at the left endpoint and to \(-\sigma\pi/2\) at the right. Consequently
\[
 \int_D A\psi_s\,ds =\int_D k\,ds-\sigma\pi.
\]
Take \(c=(\max\psi+\min\psi)/2\) and integrate by parts on each lobe. Summing the absolute values yields the necessary condition
\[
 2\sum_D\left|\int_D|k|\,ds-\pi\right|
 \le \operatorname{osc}(\psi)\int_0^L|A_s|ds
 <\left[\pi+|b/a|\log\!\left(r_{\max}/r_{\min}\right)\right]\int_0^L|A_s|ds .
\]
The strict inequality applies when curvature has a zero, because \(A=0\) there and \(A>0\) elsewhere. The lobe sum also applies at zero total turning. When curvature has no zeros, \(\alpha\) is periodic on the full period and the left side becomes \(2|\int k\,ds|\). In that case \(A\) must vary if the centre is strictly outside, since the turning of a one-sign closed curve is nonzero.

For the signed version with zeros, summing without absolute values subtracts \(\pi\) times the sum of lobe signs from \(\int k\,ds\). This equals subtraction of \(\pi\) times the sum of the adjacent signs at all even-order zeros. Opposite signs at an odd-order zero cancel in this sum. The direct lobe calculation accounts for zeros of the stress, at which a global stress angle can jump.

A regularized identity requires only a smooth periodic curvature. For \(\eta>0\), set \(B_\eta=(k^2/2+\eta)/[(k^2/2+\eta)^2+k_s^2]\). The stress \(W+\eta T\) now has strictly positive projection onto \(T\) and derivative \((F+\eta k)N\). Its relative angle \(\arctan(k_s/(k^2/2+\eta))\) is smooth periodic. Hence \(\int B_\eta(F+\eta k)\,ds=\int k\,ds\). This identity applies to each actual unit-speed closed curve and was checked from the coordinate curvature and elastic force in Lean. The lobe estimate additionally uses the similarity equation and separation. Neither the presence of two exterior fitted centres in the quadrilateral example nor the necessary angular condition establishes an actual migrating trajectory. [Lean source](../../Migration/StressAngle.lean)
