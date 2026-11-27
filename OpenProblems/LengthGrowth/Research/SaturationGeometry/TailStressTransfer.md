# Energy in each stress scale after one relaxation time

Let $X$ be one smooth global closed normal free elastic flow. Write $p=k_s$, $e=k^2/2$, $E=\int e\,ds$, $F=k_{ss}+k^3/2$, $r=\sqrt{p^2+k^4/4}$, $D=\int F^2ds$, and $Y=\int F_{ss}^2ds$. For $s>0$ put
\[
 \delta_s=E(s)-E_\infty=\int_s^\infty D,\qquad R_s=\sup_{v\ge s,x}r(v,x),\qquad
 J_s=\int_s^\infty\!\int r^2F^2ds_x\,dv .
\]
The stress supremum is finite and tends to zero. Uniformly in $a>0$ and $t\ge s+a^{-4}$, one has
\[
 \int e(t,x)\min\{1,r(t,x)^2/a^4\}\,ds_x
       \ \le C(\delta_s+J_s/a^4).                                  \tag{1}
\]
In particular $a^2\ge R_s$ gives $\int e(r/a^2)^2\le C\delta_s$ on this whole later time interval. Taking $a^2=R_s$ shows that a putative positive limiting energy must concentrate, after one actual relaxation time, at stresses negligible compared with the tail supremum. The exceptional energy at $r\ge\eta R_s$ is at most $C\eta^{-2}\delta_s$. The same conclusion with the truncated integrand in (1) holds for $a^4=J_s/\delta_s$, the dissipation-weighted mean squared stress. It remains possible for the scales carrying most of the dissipation to be much larger than the scales carrying most of the energy.

## Long-time estimate

The force evolution implies a localized-in-stress inequality
\[
                  D'+cY\le C\int r^2 F^2ds .                        \tag{2}
\]
Indeed integration of the force equation yields
\[
 D'=-2Y+5\int k^2 F_s^2+\int p^2F^2+14\int kp FF_s-(5/2)\int k^4F^2.
\]
By periodic integration by parts, $\int k^2 F_s^2=-\int k^2 F F_{ss}-2\int kp F F_s$. Cauchy–Schwarz and Young (absorbing half the original integral) give $\int k^2 F_s^2\le\varepsilon Y+C_\varepsilon\int(k^4+p^2)F^2$. The mixed term in the first line is bounded by $7\int[k^2F_s^2+p^2F^2]$. A small fixed $\varepsilon$ proves (2). [Force evolution and its integrated identities](../ForcePersistence/ForceDissipationPersistence.md)

Put $h=a^{-4}$ and choose $q\in[s,s+h]$ with $D(q)\le a^4\delta_s$ by the energy law. Integrating (2) from $q$ shows, for all $t\ge s+h$,
\[
             D(t)+\int_t^\infty Y\le C(a^4\delta_s+J_s).
\]
The [quadratic stress-scale velocity estimate](StressScaleLength.md) now implies
\[
  \int_t^\infty |(a^2\Lambda_a)'|\le C\left(\delta_s+a^{-2}\sqrt{\delta_sJ_s}\right),\qquad
  a^2\Lambda_a(\infty)=E_\infty .
\]
Let $Z$ be the left side of (1) and $R=\sqrt{r^2+a^4}$. The bound $1-a^2/R\ge c\min(1,r^2/a^4)$ gives $cZ\le E-\int e a^2/R$. The force correction in the definition of $\Lambda_a$ satisfies
\[
 \left|\frac{a^2}2\int k^3 F/R^3\right|\le C a^{-2}\sqrt{Z D(t)}.
\]
For this step factor out $a^{-2}|k|$, use $a^4 k^2/R^3\le C\min(1,r/a^2)$ from $k^2\le2r$, and apply Cauchy–Schwarz. Combining the estimates gives $cZ\le C(\delta_s+J_s/a^4)+C\sqrt{Z(\delta_s+J_s/a^4)}$. Absorption proves (1). All estimates are on the physical flow and permit degenerate curvature zeros.

## A necessary cost before scale transfer

Suppose $E_\infty>0$. At all sufficiently late times $s$ one has $L(s)^2 J_s\ge cE_\infty^3$, and hence $L(s)R_s\sqrt{\delta_s}\ge c E_\infty^{3/2}$. Choose $a^2=E(s)/(8L(s))$ and take $t=s+a^{-4}$. The length secant $|L(t)-L(s)|\le \sqrt{2E(s)(t-s)\delta_s}$ gives $L(t)\le 2 L(s)$ for late $s$, while $E(t)\ge E(s)/2$. The total energy where $r<a^2$ is at most $a^2L(t)\le E(s)/4$ because $e\le r$. Thus the left side of (1) is at least $E(s)/4$ and $J_s\ge c a^4 E_\infty$ after increasing $s$. The assertion follows. In particular a single flow with positive limiting energy would have to pay a nonzero future weighted dissipation at every late scale fixed by its own length.

These inequalities alone allow a numerical hierarchy with finite initial length. To see why a simple sum over times at which $R_s$ halves gives no contradiction, write $T=1+t$ and consider scalar functions $E=1+T^{-1/50}$, $D=-E'$, $L=C_0 T^{12/25}$ and $R=T^{-9/25}$. Assign a model energy mass $T^{-1/25}$ to stress $R$ and the rest to stress $c_0/L$, choosing fixed positive $c_0$ and ignoring a bounded initial interval. Assign $J_s=\int_s^\infty R^2D\asymp T_s^{-37/50}$ and $Y=R^2D$. Then $\int D^{-2/3}Y<\infty$, $L^2J_s\to\infty$, $R^{-2}=o(t)$, and the differential secant requirement $|L'|\le\sqrt{2ED}$ holds for sufficiently late times. The model mass on the stronger scale is bounded by $\delta_s$ for $t\ge s$. The contribution of the weaker scale to (1) is bounded by $C J_s/a^4$, since $L(t)^{-2}\lesssim J_s$. For $a^2\ge R_s$ it is bounded by $C\delta_s$ since $L(t)^{-2}/R_s^2\lesssim\delta_s$. The energy losses over successive halvings of $R$ form a summable geometric sequence. This model only checks compatibility among scalar necessary conditions; it defines no evolving geometric curve. Finiteness of the actual energy-length product and exclusion of $E_\infty>0$ on every physical flow remain open.
