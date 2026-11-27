# A fixed disk for multiply wound closed curves

Let $X$ be a smooth closed planar free elastic flow, with nonzero absolute turning number $m\ge2$. Let $L$ be the length, $B=\int k^2ds$, and $c=L^{-1}\int X\,ds$ the arclength centroid. If the initial excess satisfies
\[
 LB-(2\pi m)^2\le \pi^2/4,
\]
then no two complete time slices are strictly separated by a line. The estimate allows arbitrarily large initial $LB$, since the turning number can be arbitrarily large.

Set $R_m=2\pi m/B$, $A_m=1+1/(16m^2)$. For any times $s\le t$ the convex hull of the later slice contains the closed disk centered at $c(s)$ of radius
\[
 A_m\big(0.540 R_m(s)+0.005 R_m(t)\big).
\]
The decimals in these formulas denote exact rationals.

**Single-slice estimates.** Choose the positive orientation and write $\kappa=2\pi m/L$, $\Gamma=\kappa(X-c)$, $K=k/\kappa$, and $Z=\Gamma+N$, where $T$ and $N=iT$ are the unit tangent and normal. Set $x=\sqrt{LB-(2\pi m)^2}/(2\pi)$. All norms here are with respect to average arclength. Because the curve closes, $N$ has mean zero, as do $\Gamma$ and $Z$. The Frenet formula gives the exact derivative $Z_s=(\kappa-k)T$. Consequently $\|Z_s\|_2=2\pi x/L$ and periodic Wirtinger yields $\|Z\|_2\le x$.

For each arclength $a$, integration by parts over the period beginning at $a$ gives
\[
 Z(a)=L^{-1}\int_a^{a+L}(s-a-L/2) Z_s(s)\,ds .
\]
Hence $\|Z\|_\infty\le (\pi/\sqrt3)x < (91/50)x$ for $x>0$. The weak inequality holds also at zero. Every normal direction occurs because the tangent map has nonzero degree. Thus the support of $\Gamma$ in every direction is at least $1-(91/50)x$, while $\|\Gamma\|_\infty\le1+(91/50)x$. With $p=\Gamma\cdot N$ and $H=K\Gamma+N$, these bounds imply
\[
 \|p\|_2\le1+x,\qquad
 \|H\|_2\le x+(x/m)(1+(91/50)x).
\]
Indeed $p=Z\cdot N-1$, $H=Z+(K-1)\Gamma$, and $\|K-1\|_2=x/m$.

**Centroid displacement.** Put $F=k_{ss}+k^3/2$, $E=B/2$, and $Y=\int F^2ds$. The centroid derivative is $c'=L^{-1}\int F H\,ds$, and the dilation virial gives $E=-\kappa^{-1}\int Fp\,ds$. Since $R_m'=\pi mY/E^2$, two applications of Cauchy–Schwarz give
\[
 |c'|\le(1+x^2/m^2)\|p\|_2\|H\|_2 R_m'.
\]
In physical coordinates every support about $c$ is at least $(1+x^2/m^2)(1-(91/50)x)R_m$.

For $0\le x\le 1/4$, the drift coefficient is at most $0.540 A_m$. This follows from the increasing polynomial bound
\[
 (1+x)x\big(1+(1+(91/50)x)/m\big)
 \le (5/4)(1/4)\big(1+(1+91/200)/2\big)<0.540.
\]
The support coefficient is at least $0.545 A_m$. The function $(1+x^2/m^2)(1-(91/50)x)$ is decreasing on the given interval, since its derivative is at most $2x/m^2-91/50<0$. Integrating the centroid estimate and subtracting the displacement from the support in each direction proves the disk inclusion whenever the excess bound holds throughout the intervening time interval.

**Propagation from the initial slice.** Write $P=\sqrt{LB}$. The initial threshold gives $P-2\pi m\le(\pi^2/4)/(4\pi m)=\pi/(16m)<3/5$. The spatial curvature estimates and the variation of $LB$ exclude a first upward crossing inside $2\pi m<P\le2\pi m+3/5$. A one-sided continuity argument then yields $L(t)B(t)\le L(0)B(0)$ for every $t>0$. The integral of signed curvature is conserved because it is continuous and takes values in $2\pi\mathbb Z$. Reflection handles negative turning. [Material energy propagation](../../Migration/MultiDiskBendingInvariant.lean) · [Conservation of turning](../../Migration/MultiDiskTurning.lean)

For classical initial data the position, speed and curvature are jointly continuous down to $t=0$, and the initial speed is positive. The time-slab disk passes to $s=0$ by closedness of the later convex hull and continuity of its earlier center and claimed radius. Since $B$ is nonincreasing, every hull contains the same laboratory-frame disk about $c(0)$ of radius $(109/200)A_m R_m(0)$. Thus separation of any two full traces forces the strict initial excess $L(0)B(0)-(2\pi m)^2>\pi^2/4$. The Lean theorems are `multi_classical_earlier_disk`, `multi_classical_forward_disk` and `multi_migration_requires_initial_excess`. [Classical-flow theorems](../../Migration/MultiDiskFluxClassical.lean) · [Project audit](Verification.json)

Andrews and Wheeler prove asymptotic stability under a small initial curvature-oscillation condition and determine the sharp convergence rate of the rescaled flow. [On the planar free elastic flow with small oscillation of curvature](https://arxiv.org/abs/2509.11129v2)

