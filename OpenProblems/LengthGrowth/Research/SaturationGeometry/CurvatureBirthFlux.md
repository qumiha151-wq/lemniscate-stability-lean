# A simple creation or annihilation of two inflections carries a scale flux of exactly \(2\pi\)

Consider a compact time interval of a smooth closed planar free elastic flow in the normal material gauge. Let \(p=k_s,\ F=k_{ss}+k^3/2,\ r=(p^2+k^4/4)^{1/2}\). Assume the endpoint slices have no simultaneous zero of \(k,p\). Suppose that at each simultaneous zero in the intervening spacetime cylinder,
\[
                A=k_t\ne0,\qquad B=k_{ss}\ne0 .
\]
There are then finitely many such events. Define the signed physical spacetime measure
\[
 d\mu_a=\frac{a}{(r^2+a^4)^{3/2}}
 \left[(k^4/4-a^4)F^2+\tfrac12F(k^2F_{ss}-2kpF_s)\right]\,ds\,dt .
\]
As \(a\downarrow0\), both its signed and its absolute measures converge weakly:
\[
 \mu_a\rightharpoonup -2\pi\sum_z\operatorname{sgn}(A_zB_z)\delta_z,
 \qquad |\mu_a|\rightharpoonup 2\pi\sum_z\delta_z .
\]
The sign is positive when two simple inflections are created and negative when they annihilate. This counts events even when their net signed contribution on the full time interval vanishes. The density is the unintegrated spatial current from the [time and scale identity](DyadicForceFlux.md), before the spatial integration by parts. The event assumptions are explicit; smoothness alone does not imply them.

## Localization and normalization

Use a fixed periodic material coordinate \(u\) and let \(g=|X_u|>0\). At an event the Jacobian of \((t,u)\mapsto(k,p)\) is \(AgB\), since \(k_u=gp=0\) and \(p_u=g k_{ss}\). The inverse function theorem supplies disjoint coordinate neighborhoods of all events. They are isolated in a compact cylinder, and outside any such neighborhoods \(r\) has a positive minimum. The measures there have total variation \(O(a)\). The density \(ds\,dt\) in \((k,p)\) coordinates has limiting weight \(1/|AB|\). Also \(F=B\) and \(F_{ss}=-A\) at the event by the curvature evolution equation.

The nonnegative leading kernel \(K_a=a k^2/[2(r^2+a^4)^{3/2}]\) has constant mass in the \((k,p)\) plane. Substitute \(k=ax,\ p=a^2y\). Its mass is
\[
  \frac12\int_{\mathbb R^2}\frac{x^2\,dx\,dy}{(1+y^2+x^4/4)^{3/2}}
  =\int_{\mathbb R}\frac{x^2\,dx}{1+x^4/4}=2\pi .
\]
For the first equality integrate in \(y\) using the primitive \(y/[c\sqrt{c+y^2}]\) with \(c=1+x^4/4\). For the second, substitute \(x=\sqrt{2}v\), then invert \(v\mapsto1/v\) on the positive half-line. The integral of \((v^2+1)/(v^4+1)\) from zero to infinity is \(\pi/\sqrt{2}\) by the substitution \(w=v-1/v\). Integrability of the rescaled kernel gives concentration at the origin. Multiplication by the continuous factors \(F F_{ss}\), the coordinate density and any continuous test function yields the signed limit.

The other terms vanish in total variation. Indeed the Euclidean area of \(\{r<h\}\) is \(Vh^{3/2}\), where \(V\) is its area for \(h=1\). In a fixed event neighborhood the remaining monomials are bounded by a constant times \(r^2+a^4+r^{3/2}\), using \(|k|\le\sqrt{2r}\) and \(|p|\le r\). Integration against \(a r^{1/2}dr/(r^2+a^4)^{3/2}\), split at \(r=a^2\), gives respectively \(O(a)\), \(O(a^2)\) and \(O(a(1+|\log a|))\). The coordinate density is bounded in a smaller closed neighborhood, and its complement is away from the zeros. This proves both measure limits. For the event sign, the zeros of \(k\) near the event form a graph \(t=t(u)\) since \(A\ne0\), with \(t'=0\) and \(t''=-g^2 B/A\) there. This graph has a strict local minimum when \(AB<0\).

## What one event contributes to the band-action test

On any one fixed neighborhood containing just one event and with closure in the inverse chart, let \(I_h\) be the part where \(h/2<r\le h\). As \(h\downarrow0\),
\[
 \begin{split}
 h^{3/2}\int_{I_h}F^4/r^3\,ds\,dt
   &\longrightarrow V(2^{3/2}-1)\,|B|^3/|A|,\\
 h^{-3/2}\int_{I_h}F^2\,ds\,dt
   &\longrightarrow V(1-2^{-3/2})\,|B|/|A|.
 \end{split}
\]
This follows by substituting \(k=\sqrt{h}\,x,\ p=h y\) on the fixed annulus \(1/2<r(x,y)\le1\). The two radial integrals follow directly from \(|\{r<h\}|=Vh^{3/2}\). Thus one event already contributes a divergent sequence of raw fourth-power band actions on any tail containing it. The band test for a positive limiting energy has its restrictive content on tails without this mechanism. It is compatible with vanishing limiting energy on flows having simple events at unbounded times.

The weak and absolute measure limits here are written proofs. They distinguish concentration of the signed physical current from the one-sided fourth-power estimate and do not resolve unrestricted length growth.
