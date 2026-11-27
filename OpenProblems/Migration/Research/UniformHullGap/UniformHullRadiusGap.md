# A uniform disk inside the hull of a closed pure elastic expander

Let $X:\mathbb R/L\mathbb Z\to\mathbb R^2$ be a smooth, unit-speed immersion with $L>0$. Let $T=X'$, $N=JT$ (counterclockwise rotation), and $T'=kN$. Suppose
$$
 k''+\tfrac12 k^3=-\lambda (X-O)\cdot N,\qquad \lambda>0.
$$
There are universal constants $\delta,\eta>0$ such that, on writing $R=\max|X-O|$,
$$
 \lambda R^4\le 2+\delta \quad\Longrightarrow\quad
 \overline B(O,\eta\lambda^{-1/4})\subseteq\operatorname{conv}X(\mathbb R/L\mathbb Z).
$$
The constants are independent of period, turning number and covering multiplicity. Consequently the convex hulls of any two positively dilated copies about $O$ intersect. The proof gives existence of the constants. Their optimal values are unknown.

## The stress on a fixed disk

Scale position and arclength by $\lambda^{1/4}$ and take $O=0$. Write $p=X\cdot N$, $q=X\cdot T$, $v=k'$, and $W=\tfrac12 k^2T+vN$. Then
$$
 v'=-\tfrac12 k^3-p,\qquad p'=-kq,\qquad q'=1+kp,\qquad W'=-pN.
$$
Suppose $|X|\le2$. Given $s_0$ with $w=|W(s_0)|>0$, take $[s_0,s_0+w/8]$ on the periodic lift. Since $|W'|\le2$, we have $3w/4\le |W|\le5w/4$ there. In particular $k^2\le5w/2$ and $|v|\le5w/4$. Use bars for the averages on this interval. The identity $(X\cdot W)'=k^2/2-p^2$ and the endpoint bound $|X\cdot W|\le5w/2$ give $\overline{k^2}\le88$. Also
$$
 (kv)'=|W|^2-\tfrac34 k^4-kp.
$$
The absolute averaged endpoint term in $kv$ is at most $20\sqrt{5w/2}$, $|kp|\le2\sqrt{5w/2}$, and $\overline{k^4}\le (5w/2)\overline{k^2}$. Hence $(3w/4)^2\le22\sqrt{5w/2}+(3/4)(5w/2)\,88$. This bounds $w$, hence both $k$ and $v$, independently of the period. The argument also applies on any complete bounded trajectory. This is the fixed-disk case of the [stress-window estimate](../../../SolitonClassification/Research/RadiusBounds/UniformRadiusGapAllPitches.md).

## The projected primitive

For a unit direction $e$, set $h=X\cdot e$, $u=T\cdot e$, $n=N\cdot e$. Then $h'=u$, $u'=kn$, $n'=-ku$, $h=qu+pn$. Fix $a=2^{1/4}$. Define
$$
\begin{aligned}
 m&=(a^2+p^2+q^2)/2,& S&=k^2u/2+vn,& V&=vp+k^2q/2,\\
 J&=m(qh-S)+qkn-(1+kp)u+Vh,& \rho&=a^2+k^2/2+2q^2+kpm .
\end{aligned}
$$
Differentiation gives $J'=\rho h$ on every trajectory, using $m'=q$, $S'=-pn$, $V'=k^2/2-p^2$. If $p^2+q^2\le a^2$, then $0\le m\le a^2$ and
$$
 \rho=\tfrac12(k+pm)^2+2q^2+a^2-\tfrac12p^2m^2\ \ge\ 2q^2 ,
$$
since $p^2m^2\le a^6=2a^2$. At an interior point of any interval on which $q=0$, one has $q'=0$ and $kp=-1$. There $\rho=a^2-m+k^2/2>0$. See [the previous radius criterion](../MigrationProjectedAdjointHull.txt).

## A finite-window obstruction

If the conclusion fails, for each $j\ge1$ choose a closed normalized example with $R_j^4\le2+1/j$ whose convex hull omits a point of the closed disk of radius $1/j$. Its hull is compact. Strict separation of that point from the hull provides a unit vector $e_j$ such that $h_j=X_j\cdot e_j\ge-1/j$ everywhere. Choose the arclength origin at a **global maximum of $J_j$**. Use the same fixed $a=2^{1/4}$ for every $j$. Then $J_j(s)\le J_j(0)$ throughout $[0,6]$, however short or long the original period may be.

Every $R_j<2$, so the stress estimate bounds $k_j,v_j$ uniformly. Each of $p_j,q_j,h_j,u_j,n_j$ is bounded by 2. Their seven first derivatives are polynomials in these bounded variables. Arzelà–Ascoli on $[0,6]$ therefore gives a uniformly converging subsequence, and integrating the equations shows that the limit satisfies the same system. In particular $u^2+n^2=1$, $p^2+q^2\le a^2$, and $h\ge0$. The primitive is a polynomial in the seven variables, so $J(s)\le J(0)$ on the limiting window.

Now $J'=\rho h\ge0$ inside the interval. The initial maximum forces $J$ to be constant, hence $\rho h=0$ on $(0,6)$. If $h>0$ anywhere there, it is positive on a neighbourhood and $\rho=0$ there. The bound $\rho\ge2q^2$ then gives $q=0$ on that neighbourhood, where the strict formula gives $\rho>0$. Thus $h=0$ on the window. It follows that $u=h'=0$ in its interior, $n^2=1$, and $0=u'=kn$ gives $k=0$. Hence $q'=1$, so $q(5)-q(1)=4$. This is impossible since $|q|\le a<2$. This contradiction proves the disk assertion. Rescaling recovers the stated physical radius.

The conclusion extends the known pointwise multiplier threshold by a uniform amount. It uses a window of the actual orbit through the maximum of the primitive. Whether the centre belongs to the hull with unrestricted radius remains open.

The formal result uses a positive inverse length scale a and writes the dilation coefficient as its fourth power. Every positive coefficient has this form. The constants are existential. [Uniform disk theorem](../../Migration/UniformHullGap.lean) · [Compactness of the trajectories](../../Migration/HullTrajectoryCompactness.lean) · [Obstruction at the critical radius](../../Migration/HullCriticalWindow.lean).
