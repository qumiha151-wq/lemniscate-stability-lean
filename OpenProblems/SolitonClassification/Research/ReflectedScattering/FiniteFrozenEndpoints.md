# Finite endpoint signs for the frozen equation

Consider the arclength equations

$$
k'=v,\quad v'=-k^3/2-p,\quad p'=-kq,\quad q'=kp,\qquad p^2+q^2=1.
$$

For the initial states \((b,0,1,0)\) with \(b=-1/4\) and \(b=1\), the following bounds hold at arclength 20. Here \(h=-\mathrm{radial}\), \(I=\mathrm{transverse}/\sqrt{A}\), and \(J\) is the corrected impact of the frozen equation.

| Initial curvature | Outgoing coordinate | Corrected impact | Raw impact |
| --- | --- | --- | --- |
| \(-1/4\) | \(h>13\) | \(-0.10<J<-0.09\) | \(\lvert I\rvert<0.25\) |
| \(1\) | \(h>12\) | \(J>0.8\) | |

The Lean statements `ClosedSimilarity.FrozenStress.Endpoint.negative_end_to_end` and `positive_end_to_end` quantify over every `FrozenStress.Orbit` with the indicated four initial coordinates. The global support existence theorem realizes both initial states as canonical orbits. For every \(\lvert s\rvert\ge20\), their raw impacts satisfy \(I_{-1/4}(s)<-0.002\) and \(I_1(s)>0.52\). For each prescribed \(t\ge20\), some \(c\in(-1/4,1)\) makes the transverse stress on the same orbit vanish at both \(-t\) and \(t\), with opposite strict radial signs. The parameter \(c\) may depend on \(t\). The two formal statements are `realized_seams_on_both_tails` and `exists_transverse_zero_pair`.

The extension from this frozen scattering problem to the infinite family of closed physical expanders uses the outer entrance, seam continuation and matching arguments in the accompanying analysis.

There is also one fixed seam curvature \(c\in(-1/4,1)\) whose orbit has vanishing normalized and unnormalized transverse stress at both arclength ends. If \(B\) denotes the unnormalized transverse stress and \(h=-\mathrm{radial}\), then \(B(s)^2 h(s)\le128\) for \(h(s)\ge12\). Uniform tail control makes the limiting impact a continuous function of the seam curvature. Its endpoint values have opposite strict signs, so it has a zero. At each sufficiently high corrected radial stress level the paired incoming and outgoing sections realize every prescribed normalized impact in \([-0.002,0.52]\). The flight times vary continuously with curvature on each section. These conclusions use the same two finite certificates. [Lean theorems](../../SolitonClassification/FrozenCertifiedScattering.lean)

## Uniform error control

The stress coordinates \(R=k^2q/2+vp\) and \(B=k^2p/2-vq\) obey \(R'=-p^2\) and \(B'=pq\). Their initial conditions give \(\lvert R(t)\rvert\le20\), \(\lvert B(t)\rvert\le21\) on \([0,20]\). Since \(R^2+B^2=k^4/4+v^2\), the true solution satisfies \(\lvert k\rvert\le8\).

Use the maximum norm in the coordinates \((k,v/8,p,q)\). For a comparison path with \(\lvert k_{\rm app}\rvert\le8\), the difference of the frozen vector fields is bounded by 13 times the state difference. This estimate uses \(\lvert p\rvert,\lvert q\rvert\le1\) for the true trajectory. It follows directly from the factorization of the difference of two cubes and the two product differences in the support equations.

Each trajectory has 640 cells of width \(1/32\). In the local coordinate \(x=32(t-a)\in[0,1]\), let \(K,V,P,Q\) be integer polynomials and put \(S=2^{504}\). The comparison path in unscaled physical coordinates is \((K,V,P,Q)/S\). For each polynomial below, the checker sums the absolute values of its coefficients and divides by the displayed denominator. The second denominator accounts for the factor of eight in the norm.

| Residual polynomial | Denominator |
| --- | --- |
| \(32K'-V\) | \(S\) |
| \(2S^2(32V'+P)+K^3\) | \(16S^3\) |
| \(32S P'+KQ\) | \(S^2\) |
| \(32S Q'-KP\) | \(S^2\) |

All four ratios are at most \(2^{-432}\). The coordinate cap follows from \(\sum |K_i|\le8S\). Every right endpoint equals the next left endpoint exactly. Successive applications of Grönwall's inequality give a weighted terminal error at most

$$
\frac{2^{-432}}{13}(e^{260}-1)<2^{-20}.
$$

The final four coordinates lie in the following closed intervals, in units of \(10^{-5}\).

| Initial curvature | \(k\) | \(v\) | \(p\) | \(q\) |
| --- | --- | --- | --- | --- |
| \(-1/4\) | [341349, 341352] | [1212777, 1212781] | [−91168, −91164] | [−41097, −41093] |
| \(1\) | [−287350, −287346] | [1204546, 1204550] | [−83545, −83541] | [−54962, −54958] |

The sign inequalities follow by interval arithmetic on these four boxes, including both square roots in the normalized stress.

## Replaying the certificate

From the independent `SolitonClassification` project, run `lake build SolitonClassification.FrozenCertifiedScattering`. This builds the finite endpoint theorem, its tail estimates, the common sections, and the zero-scattering orbit. The finite endpoint theorem is also available as the target `SolitonClassification.FrozenKernelEndpoints`. Each of the 80 input files specifies 16 polynomial degrees and rational boundary data. The Lean elaborator generates a proposed polynomial path. The kernel checks every residual and every boundary equality.

For polynomial multiplication the fast checker packs signed coefficients in radix \(2^{1600}\). It independently bounds the sum of the absolute coefficients of each residual below half that radix. Under that strict bound the centered digits of the packed integer uniquely recover its coefficients. The proof of this fact justifies using a small number of integer multiplications to check the same coefficient sums as direct convolution.
