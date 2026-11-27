# Angular width as seen from an exterior expansion centre

Let $X$ be a smooth closed unit-speed immersed plane curve of period $L>0$, measured from its actual expansion centre. Let $T=X_s$, $N=JT$ and $T_s=kN$. Suppose

$$
F=k_{ss}+\tfrac12 k^3=-ap,\qquad p=X\cdot N,\qquad a>0.
$$

Suppose the origin lies strictly outside the convex hull. Set $R=\max |X|$. The directions $X/|X|$ lie in an open semicircle. In any continuous polar-angle branch on that semicircle let $w=\max\arg X-\min\arg X$. Both extrema and the maximum radius are taken over one period. Then

$$
R\sin(w/2)>(2a)^{-1/4},\qquad 0<w<\pi.
$$

The period may include multiple covers. The proof applies at every turning number and allows self-intersections.

## A pointwise sector estimate

Strict separation supplies a direction with positive projection throughout the compact image. In the oriented frame with that direction as first axis, the arctangent of the second coordinate divided by the first gives a continuous periodic polar angle $\phi$ in $(-\pi/2,\pi/2)$. Its extrema exist, so $0\le w<\pi$. Let $e$ bisect its extreme directions and put $c=\cos(w/2)>0$. At every label, with $r=|X|>0$, $h=X\cdot e$, $u=T\cdot e$, $n=N\cdot e$, and $q=X\cdot T$, one has

$$
h\ge cr,\qquad h=qu+pn,\qquad u^2+n^2=1,\qquad p^2+q^2=r^2.
$$

These equations give the identity

$$
(1-c^2)r+2cpn-\frac{p^2}{r}
=c^2rn^2+\frac{(q-cru)^2}{r}+2c(h-cr).
$$

Every summand on the right is nonnegative. The elastic stress $W=k^2T/2+k_sN$ satisfies $W_s=-apN$. Integrating its component along $e$ over one period gives $\int_0^L pn\,ds=0$. Since $h(0)=h(L)$, Rolle's theorem supplies $t\in(0,L)$ with $u(t)=h_s(t)=0$ and hence $n(t)^2=1$. The first summand is positive there and on a neighbourhood of positive length. Therefore

$$
\int_0^L \frac{p^2}{r}\,ds < (1-c^2)\int_0^L r\,ds .
$$

The proof allows either angular extremum to occur at a parameter endpoint, to occur at several labels or to be degenerate.

## The physical length scale

Set $P=\int_0^L p^2\,ds$. Since $r\le R$ and $1-c^2\ge0$, the strict inequality gives $P<(1-c^2)LR^2$. Also $q_s=1+kp$, so $\int_0^L kp\,ds=-L$. Integrating $(X\cdot W)_s=k^2/2-ap^2$ gives $\int_0^L k^2\,ds=2aP$. Cauchy–Schwarz yields

$$
L^2\le \left(\int_0^L k^2\,ds\right)P
=2aP^2 <2a L^2 R^4(1-c^2)^2 .
$$

This rules out $w=0$. Since $w<\pi$, taking positive fourth roots proves the stated lower bound. Whether a closed pure expander with an exterior centre exists remains open.

## Verification

The first Lean module proves the strict integral estimate in the existing projected Frenet frame and derives the radius bound for the project's actual Cartesian class of closed expanders. The second constructs the arctangent branch from a strictly separating unit direction, then uses its attained extrema and the attained maximum radius. The formal hypothesis of a strictly separating unit direction follows by strict convex separation of the origin from the compact convex hull. [Sector and stress estimate](../../Migration/ExteriorAperture.lean) · [Physical angular width](../../Migration/PhysicalViewingAngle.lean)
