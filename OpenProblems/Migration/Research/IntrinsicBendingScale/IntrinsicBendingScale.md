# A common convex-hull disk from local bending

Let \(\gamma\) be a smooth closed immersed planar free elastic flow, let \(K_t=\operatorname{conv}(\gamma(t))\), and extend each arclength-parametrized slice periodically to the real line. Write \(E(t)=\frac12\int k^2\,ds\), \(F=k_{ss}+k^3/2\), \(D(t)=\int F^2\,ds\), and \(M(t)=\max|k|\). The normal velocity is \(-FN\), and \(E'=-D\). The original question asks whether some pair of entire images can be strictly separated by a line. For compact planar images this is equivalent to \(K_s\cap K_t=\varnothing\). [Miura and Wheeler, introduction](https://arxiv.org/abs/2404.12619)

## Local bending and the protected interval

**Theorem.** There are universal constants \(c,C>0\). At any regular time \(s\), suppose \(r>0\) satisfies
\[
  r\sup_{a\in\mathbb R}\int_a^{a+r} k(s,z)^2\,dz\le1. \tag{1}
\]
There is a point \(p\), determined by the initial slice, such that
\[
  \overline B(p,r/12)\subset K_u\qquad(s\le u\le s+c r^4). \tag{2}
\]
In a tangential parametrization initialized by arclength, each label moves at most \(Cr((u-s)/r^4)^{3/8}\) on this interval. Constants are independent of period, turning, multiplicity, the number of passages in any spatial ball, and the global integral of \(k^2\). In particular one may take \(r=M(s)^{-1}\). A closed immersed curve has \(M(s)>0\).

**Initial width.** Fix a unit horizontal direction \(e\). At a maximum of the perpendicular projection the tangent is \(e\) or \(-e\). Follow the next arclength \(r\). For \(0\le z\le r\), Cauchy–Schwarz and (1) give \(|\theta(z)-\theta(0)|^2\le z\int_0^z k^2\le1\). Thus the tangent projection along its initial direction is at least \(1/2\), so the occupied horizontal interval has length at least \(r/2\).

For completeness pick a largest-area triangle with its vertices on the initial compact image. It exists and is nondegenerate by the width estimate. Relative to each edge, the entire image lies in the strip bounded by the lines at distance equal to the opposite altitude on either side of the edge, by maximality. For a direction \(e\), let \(\lambda_i\) be affine barycentric coordinates. Every image point has \(|\lambda_i|\le1\) and \(\sum_i\lambda_i=1\). Equivalently it lies in the triangle \(\lambda_i\le1\), which is the reflection and dilation by 2 of the chosen triangle about its centroid. If the three signed projections from that centroid are \(p_1,p_2,p_3\), their sum is zero. In this direction the original image has upper support at least \(\max p_i\) and at least its width minus its negative support. The latter negative support is at most \(2\max p_i\); writing \(h\) for the actual upper support, the width is therefore at most \(h+2\max p_i\le3h\). Consequently every upper support lies at distance at least \(r/6\) from that centroid. Moving each initial point within \(r/24\) of a later image leaves every later support at distance at least \(r/8\). This proves the disk claim with room to spare once the displacement estimate is proved.

## Uniform displacement

Rescale \(r=1\), \(s=0\), and let \(x\) be the initial arclength label, of period \(P\). We use a strictly parabolic parametrization \(Y\). With \(V=Y_x\), \(g=|V|\), \(u=V\cdot V'\), \(d=\det(V,V')\), and \(N=JV/g\), differentiation of \(k=d/g^3\) with \(\partial_s=g^{-1}\partial_x\) gives
\[
 F=g^{-4}V'''\cdot N+R,\qquad
 R=g^{-5}\det(V',V'')-7g^{-7}d'u-3g^{-7}du'
       +18g^{-9}du^2+\tfrac12g^{-9}d^3 .
\]
Primes here denote \(x\)-derivatives. Set \(a=g^{-4}\), \(H=-RN\), and solve
\[
 Y_t=-a(V)V'''+H(V,V',V''),\qquad V_t=\partial_xY_t. \tag{3}
\]
Its normal projection is exactly \(-FN\). Standard smooth short-time existence for strongly parabolic periodic systems gives the individual smooth solution while \(g>0\). Normal-flow uniqueness up to tangential reparametrization identifies its full images with the given elastic flow. The estimate below supplies a uniform continuation time even for slices whose higher derivatives and periods vary. For a parametric reduction and classical short-time theory in the more general network setting see [Dall'Acqua, Lin and Pozzi](https://arxiv.org/abs/1912.09626). On \(1/2\le g\le2\), constants depending on \(V\) only are uniformly bounded and
\[
 |H|\le C(|V'||V''|+|V'|^3).
\]

Extend all periodic fields to the line. Put \(f=V'\), \(\omega_y(x)=\exp(-\sqrt{1+(x-y)^2})\), and \(K_y(t)=\int_{\mathbb R}\omega_y|f|^2\,dx\). At \(t=0\), \(g=1\) and \(|f|=|k|\). Summing the unit interval bounds in (1) against this summable weight gives \(K_y(0)\le C_0\) uniformly. Work on the bootstrap interval \(1/2\le g\le2,\ \sup_yK_y\le2C_0+1,\ t\le1\). Equation (3) gives the exact identity
\[
 \tfrac12K_y'=\int(\omega_y f)''(-a f''+H).
\]
The derivatives of the weight through order two are bounded by \(C\omega_y\). On any unit interval \(J\) the bootstrap bounds \(\|f\|_{L^2(J^*)}\) on its concentric triple. Writing \(B_J=\|f''\|_{L^2(J^*)}\), the one-dimensional bounded-interval interpolation inequalities yield
\[
 \|f\|_{\infty,J}\le C(1+B_J^{1/4}),\qquad
 \|f'\|_{2,J}\le C(1+B_J^{1/2}).
\]
In particular \(\int_J |ff'|^2\le C(1+B_J^{3/2})\) and \(\int_J |f|^6\le C(1+B_J)\). The weights are comparable on each triple, and these triples have bounded overlap. By Young's inequality, the weighted integrals of \(|H|^2+|f'|^2+|f|^2\) are bounded by \(\epsilon\int\omega_y|f''|^2+C_\epsilon\). Absorbing the mixed terms in the exact identity gives
\[
 K_y'+c_0\int\omega_y |V'''|^2\le C,\qquad
 \int_0^\tau\!\!\int\omega_y |Y_t|^2\le C \quad(\tau\le1). \tag{4}
\]
The second assertion uses (3), the same absorption, and the integral of the first inequality. All the constants are uniform in \(y,P\).

Let \(\varphi_\ell\) be a smooth unit-mass convolution kernel supported in \([-\ell,\ell]\) for \(0<\ell\le1\). The uniform unit-interval \(L^2\) bound on \(V'\) gives \(\|V-\varphi_\ell*V\|_\infty\le C\ell^{1/2}\) at every bootstrap time, including time zero. By \(V_t=\partial_xY_t\) and (4), each pointwise change of the convolved \(V\) is bounded by \(C\sqrt{\tau}\|\varphi_\ell'\|_2\le C\sqrt{\tau}\ell^{-3/2}\). With \(\ell=\tau^{1/4}\) this gives
\[
 \|V(\tau)-V(0)\|_\infty\le C\tau^{1/8}. \tag{5}
\]
For sufficiently small universal time, (4) and (5) strictly improve both bootstrap inequalities.

Here are continuation details. Once a single period \(P\) is fixed, the bootstrap bounds the unweighted \(\|V'\|_2\) on that period, with constants now allowed to depend on \(P\). For each integer \(j\ge2\), two integrations by parts in (3) give
\[
 \tfrac12\partial_t\|V^{(j)}\|_2^2
  =\int V^{(j+2)}\cdot\partial_x^{j-1}(-aV'''+H).
\]
The leading term is \(-\int a|V^{(j+2)}|^2\). Each remaining term is a smooth bounded coefficient of \(V\) times a product of \(m\ge3\) positive-order derivatives of \(V\) whose orders sum to \(2j+4\). Only the displayed testing factor may have order \(j+2\). Use Hölder with exponent 2 on that factor and \(2(m-1)\) on each other factor. The interpolation of each \(V^{(d)}\) between \(V'\) in \(L^2\) and \(V^{(j+2)}\) in \(L^2\) uses high-norm exponent \((d-1+1/2-1/p)/(j+1)\). Their exponents sum to \((2j+3-m/2)/(j+1)<2\). Thus the errors can be absorbed leaving a finite upper bound for the derivative of each squared norm. No smooth norm can blow up on a finite bootstrap interval for the fixed individual period, and the metric is bounded below. Classical periodic continuation extends (3) throughout the common small time. Continuity of \(\sup_y K_y\) follows from the periodicity in \(y\).

Finally set \(W=Y(\tau)-Y(0)\). From (4) its local \(L^2\) norm is \(O(\sqrt{\tau})\), uniformly in position. Hence \(|\varphi_\ell*W|\le C\sqrt{\tau}\ell^{-1/2}\). By (5), \(|W-\varphi_\ell*W|\le C\ell\tau^{1/8}\). Taking \(\ell=\tau^{1/4}\) gives \(\|W\|_\infty\le C\tau^{3/8}\). Restrict the universal time so this is at most \(1/24\), and undo the length and time scalings. This proves (2).

## Energy loss before migration

The universal closed-curve stress estimate \(M^6\le2^{24} ED\) gives, for every \(a\le b\),
\[
 \int_a^b M(v)^6\,dv\le 2^{23}(E(a)^2-E(b)^2). \tag{6}
\]
The static estimate is valid even at a self-intersecting slice. [Proof and formalization scope](../../../LengthGrowth/StressCoercivity.txt)

If \(K_s\cap K_t=\varnothing\), then for **every** \(v\le s\),
\(t-v>c/M(v)^4\), since otherwise the disk based at \(v\) would lie in both hulls. Integrating its \(3/2\) power lower bound in (6) gives
\[
 E(a)^2-E(s)^2\ge 2^{-22}c^{3/2}
  \left(\frac1{\sqrt{t-s}}-\frac1{\sqrt{t-a}}\right),\qquad 0\le a<s<t. \tag{7}
\]
For \(h=t-s\le s\), take \(a=s-h\). The preceding interval \([s-h,s]\) must already have lost at least \(2^{-22}c^{3/2}(1-1/\sqrt2)/\sqrt h\) in squared bending energy. This estimate concerns physical time before the first photograph.

## All sufficiently late snapshots have expanding shared windows

For a global smooth flow write \(E_\infty=\lim_{t\to\infty}E(t)\). The static stress estimate and \(M>0\) imply \(D>0\); hence \(\delta(s)=E(s/2)^2-E_\infty^2>0\). Fix a sufficiently small universal \(\kappa>0\) and set
\[
 R(s)=\min\left(\tfrac{s}{2},\frac{\kappa}{\delta(s)^2}\right).
\]
For every \(s>0\), one disk of radius \(c_1 R(s)^{1/4}\) belongs to **every** \(K_u\) for \(s\le u\le s+R(s)\). Indeed (6) supplies \(v\in[s-R,s]\) with \(M(v)^6\le 2^{23}\delta(s)/R\). The interval of (2) based at \(v\) lasts at least \(c[R/(2^{23}\delta)]^{2/3}\), which is at least \(2R\) when \(\kappa\) is small, and its radius is at least \((2R/c)^{1/4}/12\). Both terms defining \(R(s)\) tend to infinity. Consequently, given any fixed duration and any fixed spatial radius, **all** sufficiently late starting times admit a disk of at least that radius throughout that duration.

A complementary density estimate gives polynomial windows. For any fixed \(A,B>0\), take \(\lambda>0\) small enough that \(1/(12\lambda)\ge A\) and \(c/\lambda^4\ge B\). The exceptional set \(\{s\in[T,2T]:M(s)>\lambda T^{-1/6}\}\) has measure at most \(\lambda^{-6}T\int_T^{2T}M^6=o(T)\) by (6). At every other starting time the common disk of radius \(AT^{1/6}\) persists up to \(s+BT^{2/3}\).

Equivalently let \(\sigma(s)\) be the infimum of the positive delays at which \(K_s\) and \(K_{s+\sigma}\) are disjoint, with infinite infimum for the empty set. Continuous dependence of the two hulls on their time arguments in Hausdorff distance makes disjointness an open condition. Hence \(\{\sigma(s)<h\}\) is relatively open for each \(h>0\). The pointwise bound \(\sigma(s)\ge c M(s)^{-4}\) and (6) imply
\[
 \int_S^\infty \sigma(s)^{-3/2}\,ds
 \le 2^{23}c^{-3/2}(E(S)^2-E_\infty^2).
\]
Intervals that are arbitrarily long relative to the intrinsic starting scale remain possible under these necessary conditions. Existence of any strictly separated pair stays open.

## Verification scope

The independent Migration Lean project derives the width estimate from the true arclength-normalized curvature of a periodic immersion. It proves the common-center disk conclusion under a directed image displacement bound, the admissibility of \(1/M\) under a true curvature bound, and the integration step (7) from the physical dissipation floor using the flow's actual bending derivative. The localized parabolic estimate (3)–(5), its identification with the geometric flow, the application of the previously established stress inequality, and the late-window conclusions are written analytical proofs. The report records the source hashes, compiler output and independent project-wide axiom audit.
