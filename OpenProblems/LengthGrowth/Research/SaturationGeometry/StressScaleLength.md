# A regularized length with quadratic velocity and an exact inflection-count integral

Let $X_t=-F N$, $F=k_{ss}+k^3/2$, $p=k_s$, $D=\int F^2ds$, $Y_2=\int F_{ss}^2ds$ on a smooth closed normal free elastic flow. Put $W=(k^2/2)T+pN$, $r=|W|$, so $W_s=FN$. For any fixed $a>0$ let $R=(r^2+a^4)^{1/2}$ and define
\[
 \Lambda_a=\frac12\int\left(\frac{k^2}{R}-\frac{k^3F}{R^3}\right)ds.
\]
This quantity is smooth even through degenerate inflections. Every such flow obeys the exact identity
\[
 \begin{split}
 \Lambda_a'={}&\int\left[-\frac{k^4/4+a^4}{R^3}
             +\frac{3a^4(2p^2+k^4)}{R^5}\right]F^2ds\\
 &+\int \frac{5a^4-r^2}{2R^5} F\,(k^2F_{ss}-2kpF_s)\,ds .          \tag{1}
 \end{split}
\]
In particular $|\Lambda_a'|\le C(a^{-2}D+a^{-4}\sqrt{DY_2})$. The derivative of the actual length has a first-order force term. Both terms in (1) have at least two force factors, allowing spatial derivatives. For every fixed $a$ this corrected length has finite total variation from every positive time to infinity and converges to $E_\infty/a^2$. Indeed the established force estimate gives $D\to0$, $\int D<\infty$ and $\int D^{-2/3}Y_2<\infty$, hence $\int Y_2<\infty$. Also $k,p\to0$ uniformly, so $R\to a^2$ uniformly, and $\int |k^3F|\le\|k\|_\infty^2\sqrt{2ED}\to0$. [Force dissipation and positive-time estimates](../ForcePersistence/ForceDissipationPersistence.md)

## Derivation from two moving vectors

First suppose $r>0$. Write $e=W/r$, $J$ for counterclockwise rotation through $\pi/2$, $A=k^2/(2r)$, $b=p/r$, $g=k/r$ and $Z=X+gJe$. Thus $T=Ae-bJe$, $N=be+AJe$. For a local angle of $e$ write $e_s=\psi_sJe$, $e_t=\psi_tJe$. The two entries of $W_s=FN$ give $r_s=bF$ and $\psi_s=AF/r$. Moreover
\[
 Z_s=(A-g\psi_s)e+(g_s-b)Je,\quad
 Z_t=(-Fb-g\psi_t)e+(g_t-FA)Je.
\]
The time derivative of $\oint e\cdot dZ$ is $\int(e_t\cdot Z_s-e_s\cdot Z_t)ds$, by differentiating in a fixed material coordinate and integrating the exact material differential. Since $g_s-b=-kr_s/r^2$ and $Ar_t-br\psi_t=W_t\cdot T=k k_t+pF_s$, the integrand reduces to
\[
   -k^4F^2/(4r^3)-k^2 FF_{ss}/(2r^3)+kpFF_s/r^3=Q_0,
\]
using $k_t=-F_{ss}-k^2F$. In fact $\oint e\cdot dZ=\int[k^2/(2r)-k^3F/(2r^3)]ds$.

For a smooth scalar weight $f=f(r)$ the corresponding time derivative integrand for $\oint f e\cdot dZ$ is
\[
 fQ_0+f'\left[A r_t + b^2 F^2-kF(W_t\cdot T)/r^2\right].
\]
Subtract $\frac12\int k^2\zeta(r)ds$, where $\zeta'=f'/r$. Its $r_t$ term cancels exactly. The remaining term contributed by the subtraction is $\int\zeta(kF_{ss}+k^3F/2)ds=\int[\zeta F^2-\zeta_s(kF_s-pF)]ds$. Inserting $k_t=-F_{ss}-k^2F$ leaves the three coefficients
\[
 F^2:\ -fk^4/(4r^3)+f'(2p^2+k^4)/r^2+\zeta,\quad
 k^2FF_{ss}:\ -f/(2r^3)+f'/r^2,\quad
 kpFF_s:\ f/r^3-2f'/r^2 .
\]
Taking $f=r^3/R^3$, $\zeta=-a^4/R^3$ gives the displayed $\Lambda_a$ and (1).

The intermediate exact spatial fluxes have smooth extensions through $r=0$. Explicitly $f e\cdot Z_t=-r^2pF/R^3-k\det(W,W_t)/R^3$, and the other flux is $\zeta(k F_s-pF)$. The density $f e\cdot Z_s$ also extends as $r^2k^2/(2R^3)-k^3F/(2R^3)$. Thus the underlying local identity, including these exact spatial differentials in a fixed material coordinate, extends by continuity to the boundary of $\{r>0\}$. On the spacetime interior of $\{r=0\}$ all curvature and force derivatives vanish and both sides vanish. Periodicity discards the smooth fluxes. The derivative bound follows from $k^2\le2r$, $|p|\le r$, $R\ge a^2$, and $\|F_s\|_2^2\le\sqrt{DY_2}$. The resulting mixed term $a^{-3}D^{3/4}Y_2^{1/4}$ is at most half the sum of the other two bounds.

## Integrating the scale

On any slice on which $r>0$ everywhere, write $\lambda=\sqrt r$ and $(k,p)=(\lambda u(\phi),\lambda^2u'(\phi))$. The periodic oscillator $u''=-u^3/2$, $u(0)=0$, $u'(0)=1$ has $u'^2+u^4/4=1$ and period $P$. The phase satisfies the exact relation
\[
                   \phi_s=\lambda-u(\phi)F/(2\lambda^2).
\]
Differentiate $k/\lambda$ using $r_s=u'F$. At a turning point of the oscillator the same identity follows by differentiating $p/\lambda^2$; the two oscillator derivatives never vanish together. Because $\phi_s=\lambda>0$ at $u(\phi)=0$, the degree of this map to its phase circle equals the number $n_+$ of zeros of $k$ at which $p>0$. With $C_0=\int_0^\infty(1+x^4)^{-1/2}dx$ one has
\[
  \int_0^\infty \Lambda_a\,da
  =\frac{C_0}2\int\left[\frac{k^2}{\sqrt r}-\frac{k^3 F}{2r^{5/2}}\right]ds
  =\frac{C_0}2\oint u(\phi)^2d\phi
  =\frac{C_0}2 n_+\int_0^P u^2d\phi .                             \tag{2}
\]
Indeed $\int da/R=C_0/\sqrt r$ by scaling and differentiation in $r$ gives $\int da/R^3=C_0/(2r^{5/2})$. On these slices $r$ has a positive minimum, justifying all absolute integrations. For every $a>0$, estimate (1) also bounds the variation rate of $\int_a^\infty\Lambda_b\,db$ by $C(a^{-1}D+a^{-3}\sqrt{DY_2})$ on any smooth flow, including slices with multiple zeros. The loss as $a\downarrow0$ prevents a time-uniform count estimate by this bound alone. [Entropy and the actual high-record obstruction](StressLogEntropyObstruction.md)
