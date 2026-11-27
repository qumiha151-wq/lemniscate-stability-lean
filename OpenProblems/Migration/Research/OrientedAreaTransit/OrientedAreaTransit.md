# Oriented area at both ends of a completely migrating closed elastic flow

Consider a smooth regular closed planar free elastic flow, counting the full parameter multiplicity, with normal velocity $-FN$, $F=k_{ss}+k^3/2$. Choose a unit direction $e$ and coordinates $(x,h)$ oriented so that $h=X\cdot e$ and $x_s=z=N\cdot e$. Thus $x=X\cdot(-Je)$ and $x,h$ are periodic material coordinates. Define
$$
A_t=\oint h\,dx,\qquad B_{\delta,t}=\oint\sqrt{z^2+\delta^2}\,ds,\qquad
M_{\delta,t}(\lambda)=\oint (h-\lambda)\sqrt{z^2+\delta^2}\,ds .
$$
Here $A_t$ is minus the usual oriented area for a counterclockwise simple traversal, and is defined for any smooth immersed curve. Closedness gives $\oint dx=0$, hence $A_t=\oint(h-a)\,dx$ for every constant $a$. This identity is exact for every choice of unit direction.

Suppose $s\le t$ and $h(s,\cdot)\le\lambda-g_0$, $h(t,\cdot)\ge\lambda+g_1$. For every $\delta>0$ the actual time integral of the regularized projected-height evolution satisfies
$$
\int_s^t\!\oint F\left[-\frac{(1+\delta^2)z}{\sqrt{z^2+\delta^2}}
 +(h-\lambda)k\frac{\delta^2(1+\delta^2)}{(z^2+\delta^2)^{3/2}}\right]ds_{\rm arc}\,d\tau
\ \ge\ g_1B_{\delta,t}+g_0B_{\delta,s}+|A_t|+|A_s| .
$$
In fact the time integral equals $M_{\delta,t}(\lambda)-M_{\delta,s}(\lambda)$. On the terminal slice use $a=\lambda+g_1$ and on the initial slice use $a=\lambda-g_0$. Since $|dx|\le\sqrt{z^2+\delta^2}\,ds$, each residual height integral bounds $|\oint(h-a)\,dx|=|A|$. The residual has known sign at each of the two times. In particular the two endpoint area terms have the same positive sign even if $A$ changes sign during the flow. The constants $g_0,g_1$ can be any real numbers satisfying the stated pointwise support inequalities. True separation uses positive gaps; choosing the actual endpoint extreme heights gives the strongest bound of this form.

## An absolute winding refinement in the plane

There is also a written geometric refinement at each endpoint:
$$
\int_{\mathbb R^2}|\operatorname{wind}_{X}(q)|\,dq
\ \le\ \oint |h-a|\,|dx|
\ \le\ \oint |h-a|\sqrt{z^2+\delta^2}\,ds
$$
for every $a\in\mathbb R$. To see this, fix a regular value $\xi$ of the horizontal coordinate $x$ on the compact parameter circle. The fiber contains a finite list of transverse intersections with heights $h_i$, counted at distinct parameter labels even when their geometric positions coincide. As a point moves up the vertical line, the winding is zero outside the range and jumps by an oriented unit at each label. For $y>a$ the absolute winding at $(\xi,y)$ is bounded by the number of labels with $h_i>y$, counting from above. For $y<a$ use the labels with $h_i<y$, counting from below. Integrating these two inequalities in $y$ gives the upper bound $\sum_i|h_i-a|$. Sard's theorem discards the critical horizontal values. The one-dimensional area formula for the smooth real function $x$ identifies the integral of this sum in $\xi$ with $\oint |h-a|\,|dx|$. The curve trace has zero planar measure. This proof covers self-intersections, vertical tangent degeneracy and multiple covers. It yields the same time-integral bound with $\int|\operatorname{wind}_{X_t}|$ and $\int|\operatorname{wind}_{X_s}|$ in place of the two oriented absolute areas. Equality with the oriented absolute area requires a common winding sign almost everywhere; a figure-eight traversal can have positive absolute winding area despite zero oriented area.

## Two directional heights

On every slice $W=\int (z)_+ds=\int(-z)_+ds>0$ by horizontal closure and regularity of the closed immersion. Define $H_\pm=W^{-1}\oint h(\pm z)_+ds$. These heights are weighted means of actual heights on the right- and left-going arcs. Their difference satisfies $W(H_+-H_-)=A$, and $A'=-\int F\,ds=-\frac12\int k^3\,ds$. This last identity follows directly by differentiating $\oint h\,dx$ and integrating by parts around the material circle. Equivalently $\frac{d}{dt}\oint\Psi(h)\,dx=-\int\Psi'(h)F\,ds$.

On a fixed compact time slab the signed regular-point limit in the projected-height identity gives integrated equations for almost every fixed direction. To use all subintervals simultaneously, first take rational endpoints, intersect the full-measure directional sets, and use continuity of the heights and absolute continuity of the time integrals to pass to arbitrary endpoints. The coarea estimate gives an integrable time majorant for the finite signed sums for those directions. At differentiable times with regular vertical tangencies the equations read
$$
\begin{aligned}
W H_+'&=-\int_{\{z>0\}}F\,ds+
 \sum_{z=0}(h-H_+)\operatorname{sgn}(k)F,\\
W H_-'&=\phantom{-}\int_{\{z<0\}}F\,ds+
 \sum_{z=0}(h-H_-)\operatorname{sgn}(k)F .
\end{aligned}
$$
Indeed their sum in unnormalized form is the evolution of $\oint h|dx|$ and their difference is the preceding equation for $A$. Also $W'=\sum_{z=0}\operatorname{sgn}(k)F$. The signs use oriented curvature. The two heights share the endpoint term before normalization. The calculation provides no universal sign for this term, and the possibility of migration for general closed curves remains open.

The fixed-positive-$\delta$ inequality with the two endpoint oriented absolute areas, the zero projection over a period and invariance under arbitrary constant height offsets have been verified in Lean with only the three standard axioms. [Lean source](../../Migration/OrientedAreaTransit.lean) · [Kernel check](OrientedAreaTransitVerification.json). The absolute winding refinement and the split singular evolution are written arguments only.
