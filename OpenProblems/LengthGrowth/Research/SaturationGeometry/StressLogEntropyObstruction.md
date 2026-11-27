# The logarithmic stress entropy diverges on a positive-energy plateau, but has no universal one-sided dissipation estimate

Write $p=k_s$, $z=k^2/2+ip$, $r=|z|$, $H=-\frac12\int\operatorname{Re}(z\log z)ds$, with the principal argument $\alpha\in[-\pi/2,\pi/2]$ and $z\log z=0$ at the origin. All units below may be fixed by taking the initial energy to be one. This is a continuous intrinsic entropy on every smooth curve, including open straight pieces in the immersion.

On slices with $r>0$ it is exactly the finite part of the [weighted scale integral](StressScaleLength.md), up to a fixed multiple of $E$. Namely
\[
 \lim_{A\to\infty}\left(\int_0^A a\Lambda_a da-E\log A\right)
 =\tfrac12E\log2-\tfrac14\int k^2\log r\,ds-\tfrac14\int k^3F/r^2\,ds
 =H+E(\tfrac12\log2-1).
\]
The scalar integrals are $\int_0^A a/R\,da=\frac12\operatorname{arsinh}(A^2/r)$ and $\int_0^A a/R^3\,da=A^2/(2r^2\sqrt{r^2+A^4})$. Since $\alpha_s=k^2 F/(2r^2)-k$,
\[
 \int k^3F/r^2\,ds=2\int k^2ds-2\int p\alpha\,ds,\qquad p\alpha\ge0.
\]
Equivalently $H=-\frac14\int k^2\log r\,ds+\frac12\int p\alpha\,ds$, with the continuous extension of the joint density at $z=0$. This last representation is valid without a positive stress hypothesis. Because $r\to0$ uniformly on every smooth closed free elastic flow and $E$ decreases, if $E_\infty>0$ then $H(t)\to+\infty$. A uniform upper bound on $H$ along each single flow would rule out a positive limiting energy.

## The positive derivative can be large at a genuine increasing record

For any $\sigma>0$ and any height $K$ there is a sequence of smooth closed primitive curves with initial energy one, turning number one and $U(0)>K$ for which the physical flow has $U'(0)>0$, $DL^2/E^3<\sigma$ and
\[
                    H'_+(0)/D(0)\longrightarrow+\infty .              \tag{1}
\]
The sequence has a common upper bound on $Y_2(0)=\int F_{ss}^2ds$. Both $D(0)$ and $Y_2(0)$ converge to the corresponding quantities of one fixed smooth initial curve of positive dissipation. Relative dissipation $DL^2/E^3$ and record height can thus be placed in the specified regime before making the ratio diverge. This rules out the pointwise estimate $H'\le CD$ there, including the scale-invariant version obtained by adding $E\log E$. It also rules out a uniform integrated version on every initial strict-record interval, by taking its right derivative. Controlling the cumulative entropy excursions along one positive-energy trajectory remains an open possibility.

To see the origin of the obstruction let $v(x)=\sin x-\sin(3x)/9$, $g(x)=-\cos x+\cos(3x)/27$, so $g'=v$. The zeros of $v$ modulo $2\pi$ are $0,\pi$, both simple, since $v=\sin x(2/3+4\sin^2x/9)$. Its third derivatives there are $2,-2$. Integration over the two sign intervals gives
\[
                 -\int_0^{2\pi}\operatorname{sign}(v) v^{(4)} dx=8.  \tag{2}
\]
This is an instant of increasing total variation of a curvature profile under the principal biharmonic term. We realize it while preserving the stringent geometric restrictions in (1).

First fix small $\delta>0$ and take $M$ complete cells of $w_\delta$ as defined in [the rotating-cell construction](CheapRecordRuns.md), each of length $2\pi$, each with $F=\delta k$ and mean curvature zero. Append a connector of bounded length, smoothly continuing the endpoint jets by cutting off the same bounded periodic wave at either end. Leave a nonempty open straight interval in its interior. On a disjoint part of the connector add one fixed compactly supported smooth bump times a scalar to adjust its total curvature to $2\pi/B$, for a fixed integer $B\ge2$. The scalar, connector length and all fixed derivative norms stay bounded as $\delta\to0$, $M\to\infty$, since the endpoint jets are phases of the same smooth family and the unadjusted connector integral is bounded. Repeating this block $B$ times with successive tangent directions rotated by $2\pi/B$ closes the curve exactly. Full turning one excludes a nontrivial cover. With averages now taken over the entire period, this gives, for large $M$,
\[
 E/L\asymp1,\quad \langle kF\rangle=\delta\langle w_\delta^2\rangle+O(M^{-1}),\quad
 \langle F^2\rangle=\delta^2\langle w_\delta^2\rangle+O(M^{-1}).
\]
Choose $\delta$ small and then $M\gg\delta^{-2}$ large enough. The formula $U'/L^2=(E/L)\langle kF\rangle-\langle F^2\rangle$ shows that $U'>0$, $DL^2/E^3=O(\delta^2)<\sigma$ and $U>K$, with strict margins in all three statements. Keep the resulting background and $B$ fixed through the following construction.

In its straight interval take a nonnegative nonzero smooth cutoff $\chi$ with compact support. Let $G$ be a smooth periodic primitive of the zero-mean $g$ above. Add the curvature
\[
          b_N(s)=\epsilon N^{-1}\partial_s[\chi(s)G(Ns)],\qquad \epsilon=N^{-9/2},
\]
on each block. Its integral vanishes identically, so the prescribed cell rotation and exact closure persist. Through orders $0\le j\le5$ its derivatives equal $\epsilon N^j\chi g^{(j)}(Ns)+O(\epsilon N^{j-1})$. In particular $b_N\to0$ in $C^4$, so $E,L,\int kF,D,Y_2$ converge to their background values, preserving the strict inequalities. The fifth curvature derivative drives a different response in $H$.

Let $h(k,p)=-\operatorname{Re}(z\log z)/2$. Away from the origin $h_k=-k(\log r+1)/2$, $h_p=\alpha/2$. These two derivatives are locally bounded in $(k,p)$ even near the origin; for $h_k$ use $r\ge k^2/2$. Thus $h$ is locally Lipschitz, also at zero by continuity. In a smooth temporal path through $(0,0)$ its right derivative exists and equals $\pi|p_t|/4$: the $k^2\log r$ term is $o(t)$ there and $p\alpha/t\to\pi|p_t|/2$ if $p_t\ne0$, with the same limiting formula if $p_t=0$. Bounded convergence of the time difference quotients on a compact slice justifies differentiating the integral from the right even if there are straight intervals or degenerate inflections.

In the added ripple $k=O(\epsilon)$, $p=O(\epsilon N)$, $F=O(\epsilon N^2)$, and the material identities $k_t=-F_{ss}-k^2F$, $p_t=-F_{sss}-3kpF-k^2F_s$ give
\[
 k_t=O(\epsilon N^4),\qquad p_t=-\epsilon N^5\chi g^{(5)}(Ns)+O(\epsilon N^4+\epsilon^3N^3).
\]
The $h_k k_t$ term integrated on the ripple costs $O(\epsilon^2N^4(1+|\log\epsilon|))$: throughout it $r=o(1)$ and $|k\log r|\le C\epsilon(1+|\log\epsilon|)$. The measure derivative adds $h kF$ of still smaller order since $|h|\le C(\epsilon^2|\log\epsilon|+\epsilon N)$. At points where $k=p=0$, the right derivative contribution is nonnegative. Outside the marked straight interval the initial jets and motion of the curvature are those of the fixed background and its derivative contribution is bounded independently of $N$.

In the weighted $L^1(ds)$ mean with weight $\chi$, $\alpha$ differs from $(\pi/2)\operatorname{sign}(v(Ns))$ by a quantity tending to zero. Indeed on $\chi\ge\eta$ and $|v(Ns)|\ge\eta$ one has $p=\epsilon N\chi v(Ns)+O(\epsilon)$ and $k^2=O(\epsilon^2)$, giving uniform convergence there for fixed $\eta>0$. The regions $\chi<\eta$ have small weight. The fraction with $|v(Ns)|<\eta$ is $O(\eta+N^{-1})$ by simplicity of the two zeros. The same argument covers points $k=p=0$ by giving $\alpha$ any bounded value there; dropping their nonnegative contribution gives a lower bound. Periodic averaging and (2) now give, per ripple,
\[
   H'_+(0)\ \ge\ \frac\pi4\epsilon N^5\left[\frac8{2\pi}\int\chi\,ds+o(1)\right]-O(1).
\]
As $\epsilon N^5=\sqrt N$, (1) follows. To fix initial energy exactly, dilate by the initial $E_N$, which tends to a positive finite limit. Under dilation by $\ell$, $H\mapsto\ell^{-1}(H+E\log\ell)$ and $D\mapsto\ell^{-5}D$, so the ratio $H'/D$ merely shifts by $-\log\ell$. The same reasoning applies to the invariantly normalized logarithm. Each flow has $U'>0$ on a nonempty initial interval by smoothness, hence every time there is an increasing record. An integrated universal estimate on all such intervals would imply the false initial right derivative bound. These examples do not yield an unbounded-product orbit.
