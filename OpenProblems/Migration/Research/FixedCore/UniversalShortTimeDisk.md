# A physical disk shared by all early convex hulls

Write \(K_t=\operatorname{conv}X(t)\) for a smooth closed immersed planar free elastic flow with material velocity \(-FN\), \(F=k_{ss}+k^3/2\). Put \(E_t=\tfrac12\int k^2ds\). Fix an initial time \(s\). The result applies to every initial shape and turning number.

**Theorem.** There is a point \(p\), determined by \(X(s)\), with the following property for every \(0<\eta<2/3\):
\[
 (t-s)E_s^3(E_s-E_t)<C(\eta),\qquad
 C(\eta)=\frac{\eta^3}{(\pi+\sqrt{2\eta})^2}
 \quad\Longrightarrow\quad
 \overline B\!\left(p,\frac{2/3-\eta}{E_s}\right)\subseteq K_t .
\]
The quantity on the left is nondecreasing in \(t\), so the same bound holds throughout the interval ending at \(t\). In particular, the single physical disk of radius \(1/(3E_s)\) is contained in all convex hulls during
\[
 0\le(t-s)E_s^4 < \frac{1}{27(\pi+\sqrt{2/3})^2}.
\]
The theorem includes \(s=0\) for the forward flow, with the geometric PDE imposed only for positive times, joint right continuity of the positions, and right continuity of the bending energy.

## A center determined by one slice

The static strip estimate gives \(E_s W_s(e)\ge2\) for the width in every unit direction \(e\). Choose three points \(a,b,c\) on the initial curve maximizing the absolute signed area of their triangle. A maximizer exists by compactness and has positive area because all projected widths are positive. Let \(p=(a+b+c)/3\).

For any point \(z\) on the initial curve its barycentric coefficients \(\lambda_i\) relative to this triangle sum to one. Each \(\lambda_i\) is the quotient of the signed area after one vertex is replaced by \(z\) by the original signed area. Thus \(|\lambda_i|\le1\). In a unit direction \(e\), let \(h\) be the largest height of the initial curve and let \(v_i\) be the vertices. Then
\[
 e\cdot z=3e\cdot p-\sum_i(1-\lambda_i)e\cdot v_i
 \ \ge\ 3e\cdot p-2h .
\]
Hence \(h-e\cdot p\ge W_s(e)/3\ge 2/(3E_s)\) in every direction.

## Dissipation cost for a decrease in support height

Let \(d\in(0,W_s(e)]\), \(h=\max X(s)\cdot e\). If \(\max X(t)\cdot e\le h-d\), then
\[
 (t-s)(E_s-E_t)\ \ge\
 \frac{d^3}{(\pi+\sqrt{2E_s d})^2}.
\]
Take a nonnegative \(C^1\) height cutoff that vanishes below \(h-d\), equals \(\sin^2(\pi(z-h+d)/(2d))\) in \([h-d,h]\), and has values in \([0,1]\) and derivative bounded by \((\pi/d)\sqrt\chi\) on the rest of the line. Both arcs joining a maximum to a minimum traverse the transition interval. On each arc the arclength cutoff mass bounds the integral of the cutoff in the height coordinate, which equals \(d/2\). The initial mass \(m(s)\) is therefore at least \(d\), and \(m(t)=0\).

Normal velocity, variation of arclength and Cauchy–Schwarz give \(|m'|\le(\sqrt{2E_s}+(\pi/d)\sqrt m)\sqrt{\int F^2ds}\). Integrate the derivative of \(\int_0^m(\sqrt{2E_s}+(\pi/d)\sqrt y)^{-1}dy\) and use \(E'=-\int F^2ds\). This yields the displayed cost. Setting \(d=\eta/E_s\) turns its right hand side into \(C(\eta)/E_s^3\). Under the strict cost hypothesis each support height at time \(t\) therefore exceeds \(e\cdot p+(2/3-\eta)/E_s\). Directional separation proves the actual convex hull inclusion.

For the forward initial time the support heights and the energy have their right limits at zero. Choose \(\delta<\eta\) sufficiently close to \(\eta\) to retain the strict cost hypothesis. Apply the interior result for recession by \(\delta/E_v\) from positive times \(v\downarrow0\), using the initial point attaining the chosen height. The strict margin between \(\delta\) and \(\eta\) gives the same inclusion at the original initial time.

## What happens when the losses on successive intervals are added

The actual once-covered expanding circle with radius \(R\) satisfies \(R'=1/(2R^3)\) and \(E=\pi/R\). These follow from \(k=1/R\), the inward normal, and \(F=1/(2R^3)\). From radius \(a\) to radius \(b\ge a\),
\[
 \Delta t\,\Delta E
 =\frac{\pi}{2}(b-a)^2\frac{(b+a)(b^2+a^2)}{ab}
 \ \ge\ \frac{\pi}{2}(b-a)^3 .
\]
To certify a worst-case support loss of at most \(d\) from just the integral cost requires \(d^3/(\pi+\sqrt{2E_s d})^2\ge\Delta t\,\Delta E\). It follows that \(d\ge\pi\,2^{-1/3}(b-a)>2(b-a)\) for \(b>a\). For every finite partition the sum of the resulting loss budgets is at least twice the growth in radius. As the expanding circle grows indefinitely, such sums exceed every fixed initial support margin. Its geometric center actually stays fixed. Thus summing these unsigned recession estimates cannot establish a common center on arbitrary time intervals. The unrestricted long-time migration question remains open.
