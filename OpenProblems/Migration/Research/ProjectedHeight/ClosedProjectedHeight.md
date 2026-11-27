# The projected-height moment and the cost at vertical tangencies of a closed elastic flow

Take any smooth closed immersed free elastic flow on a compact time interval $[0,T]$. Fix a unit vector $e$, let $h=X\cdot e$, and use coordinates in which $e$ is vertical. Write $z=N\cdot e$, $w=T_{\rm tan}\cdot e$, where $T_{\rm tan}=X_s$ and $N=JT_{\rm tan}$. Thus $z$ is the horizontal component of the oriented tangent, $z^2+w^2=1$, $h_s=w$, $z_s=-kw$ and $w_s=kz$. All spatial integrals use actual arclength and count parameter multiplicity. Measurements of opposite sides of a given line use the same real height $\lambda$ at both times.

## A smooth identity for every direction

For $\delta>0$ define
$$
\psi_\delta(z)=\sqrt{z^2+\delta^2},\quad
A_\delta(z)=\frac{(1+\delta^2)z}{\sqrt{z^2+\delta^2}},\quad
D_\delta(z)=\frac{\delta^2(1+\delta^2)}{(z^2+\delta^2)^{3/2}} .
$$
Then for the moment $M_\delta(t)=\int(h-\lambda)\psi_\delta(z)\,ds$ one has
$$
M_\delta'(t)=-\int F A_\delta(z)\,ds+
             \int (h-\lambda) kF D_\delta(z)\,ds . \tag{1}
$$
This identity needs no regularity assumption on the vertical tangency set and applies in any material parametrization. Indeed its terms are geometric, so use the normal gauge. In that gauge $(ds)_t=kF\,ds$, $h_t=-Fz$, and $z_t=F_s w$ by the time derivative of $N$. For any smooth weight $\psi$ differentiate under the integral and integrate the $F_s$ term by parts around the parameter circle. The resulting two coefficients of $-F$ and $(h-\lambda)kF$ are $z\psi+(1-z^2)\psi'$ and $\psi-z\psi'+(1-z^2)\psi''$, respectively. For $\psi=\psi_\delta$, differentiation gives $A_\delta$ and $D_\delta$.

## A balance on actual vertical tangencies for almost every direction

Define $B(t)=\int|z|\,ds$, $J(t)=\int z^2\,ds$ and $M(t)=\int(h-\lambda)|z|\,ds$. Both $B$ and $J$ are positive since a closed regular curve cannot lie in a vertical line. For almost every unit direction $e$, simultaneously for every $\lambda$, there is an exact two-time formula:
$$
M(T)-M(0)=-\int_0^T\int F\,\operatorname{sgn}(z)\,ds\,dt
  +2\int_0^T\sum_{s:\,T_{\rm tan}(s,t)=\pm e}
       (h(s,t)-\lambda)\operatorname{sgn}(k(s,t))\,F(s,t)\,dt . \tag{2}
$$
At almost every time for each such direction the sum is finite and all the displayed tangent labels have $k\ne0$. Formula (2) makes no assumption of persistence or of a uniform bound on the number of these labels.

To justify the limit, integrate (1) over time. The endpoint moments converge uniformly in $\delta$ for fixed $e,\lambda$, since $0\le\psi_\delta(z)-|z|\le\delta$. The bulk term converges by dominated convergence with $\operatorname{sgn}(0)=0$. For $b$ equal to any of $1,X_1,X_2$, push $\operatorname{sgn}(k)bF\,|k|\,ds\,dt$ onto the direction circle by the spatial Gauss map $T_{\rm tan}$, integrating afterwards in time. The one-dimensional area formula on each slice gives an $L^1$ density
$$
g_b(\alpha)=\int_0^T \sum_{s:T_{\rm tan}(s,t)=(\cos\alpha,\sin\alpha),\,k\ne0}
                     \operatorname{sgn}(k(s,t))\,b(s,t)F(s,t)\,dt .
$$
Indeed its $L^1$ norm is at most $\int_0^T\int |k b F|\,ds\,dt$. The summation is understood through the area formula with each parameter preimage counted. Sard's theorem on the circle and Fubini's theorem imply that, for almost every direction, almost every time slice has only regular preimages of that direction and its antipode. A discrete closed subset of the compact parameter circle is finite.

For $e=(\cos\nu,\sin\nu)$ the tip term uses the circular kernel $D_\delta(\sin(\nu-\alpha))$. As $\delta\downarrow0$ it concentrates at $0,\pi$, with mass $2$ at each. For example integrate near zero with $v=\sin\alpha$: the kernel $\delta^2(\delta^2+v^2)^{-3/2}$ on the line has integral $2$, and the change-of-variable factor tends to one near zero. The angular kernels are even and decreasing away from each peak up to the midpoint, which gives convergence at Lebesgue points by the approximate identity theorem. The three densities $g_1,g_{X_1},g_{X_2}$ have common Lebesgue points at $\nu$ and $\nu+\pi$ for almost every $\nu$. Combining them linearly with the coordinates of $e$ and with $\lambda$ proves the asserted tip limit and (2).

## Necessary signed stress for complete migration

Suppose initially $h\le\lambda-g_0$ and finally $h\ge\lambda+g_T$, with $g_0,g_T>0$. Strict separation on compact images persists in an open interval of directions, so (2) is available for almost every direction in that interval with an appropriate line height. Put $\Delta E=E(0)-E(T)$, $E=\tfrac12\int k^2\,ds$, and $L(t)=\int ds$. Then

$$
2\int_0^T\sum_{T_{\rm tan}=\pm e}(h-\lambda)\operatorname{sgn}(k)F\,dt
\ \ge\ g_T B(T)+g_0 B(0)
-\sqrt{\Delta E\int_0^T\left(L(t)-\frac{B(t)^2}{J(t)}\right)dt} . \tag{3}
$$

Indeed $M(T)-M(0)\ge g_T B(T)+g_0B(0)$. Translation invariance of the elastic energy, equivalently the arclength derivative of the elastic stress, gives $\int Fz\,ds=0$ on each closed slice. Subtract $[B(t)/J(t)]z$ from $\operatorname{sgn}(z)$ in the bulk integral of (2). Its squared spatial norm is $L(t)-B(t)^2/J(t)$ for the regular directions and almost every time. Cauchy–Schwarz and the energy identity $\int_0^T\int F^2\,ds\,dt=\Delta E$ now prove (3). At a vertical tangency the actual geometric velocity is horizontal and its absolute value equals $|F|$. Thus when its right-hand side is positive, (3) forces a signed contribution from these points.

For exceptional directions the smooth formula (1) still holds. Neither the identities nor the lower bound give an unconditional sign for the tip term, so the unrestricted migration question for closed curves remains open.

Lean verifies the fixed-positive-$\delta$ evolution (1) from the project's smooth periodic immersion and actual normal velocity equation. It also verifies its two-time integral and the necessary lower bound $g_T B_\delta(T)+g_0B_\delta(0)$ under complete endpoint separation, where $B_\delta(t)=\int\psi_\delta(z)\,ds$. The singular limit (2) and inequality (3) have the written proofs above. [Lean evolution identity](../../Migration/ProjectedHeightEvolution.lean) · [Lean endpoint bound](../../Migration/ProjectedHeightTransit.lean) · [Verification record](ProjectedHeightVerification.json)
