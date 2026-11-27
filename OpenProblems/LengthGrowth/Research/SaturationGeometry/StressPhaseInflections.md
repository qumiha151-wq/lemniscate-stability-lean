# Strong transverse inflections and length along a physical closed flow

Let a smooth regular closed plane curve have arclength $s$, length $L$, signed curvature $k$, elastic force $F=k_{ss}+k^3/2$, and stress magnitude $r=(k_s^2+k^4/4)^{1/2}$. Write $E=\int k^2ds/2$, $D=\int F^2ds$, $J=\int |F|ds$, $M=\int r\,ds$. For $\eta>0$ let $N_\eta$ count the distinct parameter values on one period at which $k=0$ and $|k_s|\ge\eta E/L$. This count is finite by nondegeneracy and compactness and ignores arbitrarily many weaker or degenerate changes of sign.

There exist absolute $\eta,c>0$ such that every such slice satisfies
\[
 D\ \ge\ c\min\{E^3/L^2,\ E^5/N_\eta^6\}.                       \tag{1}
\]
For $N_\eta=0$ take the second entry as infinity. The same bound holds with only the positively crossing zeros in the count, or with only negatively crossing zeros, after adjusting the absolute constant. This gives two consequences on genuine smooth global closed free elastic flows.

* If the limiting bending energy is positive, for each finite $K$ the late set $\{t:N_\eta(t)\le Kt^{1/6}\}$ has finite logarithmic measure $\int dt/t$. In particular a bounded number of strong transverse inflections on a set of infinite logarithmic measure rules out a positive limiting energy.
* If $N_\eta(t)\le C(1+t)^\alpha$ on a tail, with $0\le\alpha<1/6$, the length satisfies $L(t)=O((1+t)^p)$ with $p=(1/2+3\alpha\delta)/(1+\delta)<1/2$, where $\delta>0$ is a universal constant. Both conclusions permit an unbounded number of weak inflections. These conditions do not give the unrestricted fourth-root length bound.

## A phase computation on any closed curve

Normalize the unforced oscillator by $U''=-U^3/2$, $U(0)=0$, $U'(0)=1$. Its closed smooth energy oval $U'^2+U^4/4=1$ is traversed regularly once in its least period $P$. Separation and reflection at its turning points give the two simple zeros $0,P/2$ modulo $P$. Define $\mu=P^{-1}\int_0^P U^2/2>0$. Where $r>0$ put $\lambda=\sqrt r$ and write $(k,k_s)=(\lambda U(\phi),\lambda^2U'(\phi))$. The phase modulo $P$ depends smoothly on the normalized point on the oval, including the two turning points: the tangent vector $(U',-U^3/2)$ never vanishes on the oval. All estimates below are uniform by compactness there.

For the unforced vector field in the $(k,k_s)$ plane, $\lambda_s=0$ and $\phi_s=\lambda$. The actual field differs by $(0,F)$. Differentiating $r$ gives $|r_s|\le |F|$, hence $|\lambda_s|\le |F|/(2\lambda)$. At fixed $k$ the derivatives with respect to $k_s$ of $(k/\lambda,k_s/\lambda^2)$ are bounded by $C/\lambda^2$. Consequently $|\phi_s-\lambda|\le C|F|/\lambda^2$. At a zero with $r>0$ differentiation of $k=\lambda U(\phi)$ gives **exactly** $\phi_s=\lambda$, since $k_s=\lambda^2 U'(\phi)$ and $U'=\pm1$. Each such crossing is in the positive phase direction.

Fix a smooth cutoff $\chi$ equal to zero on $[0,1]$, equal to one on $[4,\infty)$, and between zero and one. Fix $a>0$ and set $w=\chi(r/a^2)$. For any bounded smooth periodic $b(\phi)$, the periodic scalar $w\lambda b$ (extended by zero at low stress) satisfies
\[
 |(w\lambda b)_s-wr b'|\le C_b |F|/a .                           \tag{2}
\]
Indeed the term with $\chi'$ is supported where $a\le\lambda\le2a$. The amplitude and phase derivative errors are at most $C|F|/\lambda$ wherever $w$ is nonzero. The same bound is valid between jumps of a bounded piecewise smooth $b$ with bounded derivative.

First choose a periodic primitive $b'=U^2/2-\mu$. Integrating (2) around the closed period, and bounding the complementary low-stress region by $r\le4a^2$, gives
\[
 |E-\mu M|\le C(a^2L+J/a),\qquad |E-\mu M|^3\le C L J^2.         \tag{3}
\]
For the optimized estimate take $a=(J/L)^{1/3}$; the case $J=0$ follows by a limit. Thus when $DL^2/E^3\to0$, the actual mass ratio $M/E$ tends to the oscillator value $1/\mu$.

Next fix either the rising phase zero or the falling phase zero, and use the periodic sawtooth $b$ with derivative $1/P$ between consecutive copies of that phase and jump $-1$ at each copy. On the part where $w\ne0$ the corresponding jumps of $w\lambda b$ have size $-w\lambda$, by the exact direction of phase crossing at zeros. There are only finitely many zeros with $r\ge a^2$ by compactness and transversality. On the complementary region the product is identically zero. Periodic integration of (2), including these jumps, yields for either sign
\[
 \left|\frac MP-\sum_{\substack{k(z)=0\\ \pm k_s(z)>0}}
              \chi(|k_s(z)|/a^2)\sqrt{|k_s(z)|}\right|
       \le C(a^2L+J/a).                                             \tag{4}
\]
Weak or degenerate zeros cannot affect this formula.

Choose $a^2=\eta E/L$. Since $r\ge k^2/2$, $M\ge E$. As $J\le\sqrt{LD}$, the error in (4) is at most $CE(\eta+\eta^{-1/2}\sqrt{DL^2/E^3})$. First fix $\eta$ small enough that the first term is at most $E/(4P)$. If $DL^2/E^3$ is below a sufficiently small absolute constant, the sum on the left of (4) is at least $E/(2P)$. The [physical slope estimate](../../LengthGrowth/ActualFlow/ForceRateSlope.lean) gives
\[
 \|k_s\|_\infty^2\le 16416(ED)^{2/3}+4E^{1/4}D^{3/4}.
\]
In this low-dissipation case $D/E^5=(DL^2/E^3)/(EL)^2\le1$ since $EL\ge2\pi^2$. The second term is bounded by $4(ED)^{2/3}$. Each counted zero contributes at most $C(ED)^{1/6}$, so $N_\eta\ge c E^{5/6}D^{-1/6}$, for either sign separately. Together with the complementary high-dissipation case this proves (1).

## A second proof of the inflection lower bound

Retain $w=\chi(r/a^2)$ and write $p=k_s$. The piecewise smooth periodic function $\operatorname{sgn}(k) w p/\sqrt r$, extended by zero on $r\le a^2$, jumps upwards by $2w\sqrt{|p|}$ at each retained zero. Between jumps its derivative is
\[
 -w\frac{|k|^3}{2\sqrt r}+
 \operatorname{sgn}(k)\left(\frac{wF}{\sqrt r}
              +p\left[\frac{\chi'(r/a^2)}{a^2\sqrt r}
                         -\frac{w}{2r^{3/2}}\right]r_s\right).
\]
The terms with $r_s$ or $F$ are bounded by $C|F|/a$, using $|p|\le r$ and $|r_s|\le |F|$. Thus periodicity equates twice the total weighted zero count to the integral of $w|k|^3/(2\sqrt r)$ within $CJ/a$. Without the cutoff, Hölder gives $\int |k|^3/\sqrt r\ge (2E)^{3/2}/\sqrt M$; take the quotient as zero at zero stress. Restoring the cutoff costs at most $Ca^2L$ since $k^2\le2r$. In the small-$DL^2/E^3$ case the [formal stress-mass estimate](../../LengthGrowth/ActualFlow/PhysicalStressMass.lean) gives $M\le C E$. Taking the same successive small choices of $\eta$ and the dissipation threshold gives $\sum w\sqrt{|p|}\ge cE$. To distinguish the signs, the jump sum for the periodic observable $\mathbf{1}_{k>0}w\sqrt r$ equals the weighted count of increasing zeros minus that of decreasing zeros. Its derivative away from jumps has absolute integral at most $CJ/a$. The two separate weighted counts are therefore each bounded below by a fixed multiple of $E$, after decreasing the dissipation threshold once more. Only the finitely many zeros with $r\ge a^2$ enter either calculation. This gives (1) by the same pointwise slope bound.

## Consequences for the evolution

On the physical flow $E'=-D$ and $|L'|^2\le2ED$. Thus $\int_0^\infty D<\infty$, $\int_0^\infty |L'|^2<\infty$ and $L(t)=o(\sqrt t)$ by splitting at a fixed late time and applying Cauchy–Schwarz. If $E_\infty>0$, (1) implies $D(t)\ge c_{K,E_\infty}/t$ at all sufficiently late times at which $N_\eta(t)\le K t^{1/6}$. Integration proves the first assertion. For measurability the set where at least $n$ zeros exceed or meet the continuous threshold is Borel: restrict to compact time intervals and impose pairwise circular distances at least $1/j$ on the $n$ labels, then project the compact incidence sets and take their countable union. The material parametrization has positive speed and the threshold stays positive.

Write $U=EL$ and take $0<\delta<\min(1,\sqrt{c/2})$. Whenever $U\ge N_\eta^3$, (1) gives $D\ge cE^3/L^2$. Consequently
\[
 (EL^\delta)'=L^\delta(-D+\delta E L'/L)\le0
\]
using $|L'|\le\sqrt{2ED}$. In the alternative case under the assumed count bound, $EL^\delta=E^{1-\delta}U^\delta\le C'(1+t)^{3\alpha\delta}$. The latter bound holds up to an enlarged constant at all late times: on the open set where $EL^\delta$ exceeds this nondecreasing barrier its derivative is nonpositive. Incorporate the initial value at the start of the tail and apply the mean value theorem on each excess component. If $L(t)$ exceeds twice the length at that starting time, take the last earlier time $s$ with $L(s)=L(t)/2$. The [physical secant](../../LengthGrowth/ActualFlow/PhysicalSaturationGap.lean) gives $L(t)/2\le \sqrt{t-s}\,E(s)\le C\sqrt t(1+t)^{3\alpha\delta}/L(t)^\delta$. This proves the exponent in the second assertion, also when the threshold is exceeded by only one type of crossing.

## The remaining angular production cost

Let $A(t)=\int |k|ds$ and $Y=\int F_{ss}^2 ds$. The material curvature identity $(k\,ds)_t=-F_{ss}ds$ implies $|A'|\le\sqrt{LY}$ almost everywhere, and the more precise [directional formula](FiniteClockAngularCrossings.md) represents the signed change by the net angular velocity at inflections. The force evolution gives [the finite budget](../ForcePersistence/ForceDissipationPersistence.md) $\int_1^\infty D^{-2/3}Y<\infty$. Hence
\[
 |A(t)-A(s)|\le\left(\int_s^t D^{-2/3}Y\right)^{1/2}
                    \left(\int_s^t L D^{2/3}\right)^{1/2}.
\]
These scalar estimates still permit the growth just forced by (1). For example, on $t\ge1$ the scalar rates $E=1+t^{-1/24}$, $D=-E'$, $L=t^{11/24}$, $Y=D^{5/3}$ and $A=t^{25/144}$ satisfy the indicated tail integrability, the energy–length secant differential inequality for all sufficiently late times, and the two angular and curvature bounds $|A'|\le\sqrt{LY}$ and $E^{5/6}D^{-1/6}\lesssim A\le\sqrt{2EL}$. A strong crossing count of order $t^{25/144}$ also meets (1) up to absolute constants. Even a net production rate of size $A'$ shared among that many inflections only calls for individual angular speeds of order $1/t$, with integrable $4/3$ power. These scalar functions serve to compare estimates. A genuine curve realizing them has not been constructed. Excluding a positive limiting energy still requires information about the actual geometry or dynamics of inflection production.

The phase and long-time statements in this note are written proofs. The separate Lean modules PhysicalStressMass and StressBandMass verify the cubic one-sided stress-mass and sampling-band bounds on each actual time slice.
