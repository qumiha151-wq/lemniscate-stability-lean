# A common disk for all times at initial bending defect at most four

Let \(X\) be any smooth closed immersed free elastic flow in the plane. Write \(L=\int ds,\ B=\int k^2ds,\ c=L^{-1}\int X\,ds,\ R_E=2\pi/B\). If \(L(0)B(0)\le4\pi^2+4\), then for every \(0\le s\le t\),
\[
 \overline{B}\!\left(c(s),\frac45R_E(s)+\frac1{200}R_E(t)\right)
 \subseteq \operatorname{conv}(X(t)).
\]
In particular the convex hulls of the two whole curves meet. No straight line can put the two time slices in opposite strict half-planes. The radius uses physical coordinates and the center is the earlier arclength centroid.

The [signed evolution estimate](../../../LengthGrowth/Research/DefectFour/DefectFour.md) gives \(0\le d(t):=LB-4\pi^2\le4\) at every time. We sharpen the support and centroid estimates in Novaga's proof, which establishes non-migration for initial defect at most \(8/3\). [Novaga, §§2 and 4](https://arxiv.org/html/2611.07242v1#S4)

## Directional support and outer radius

At a fixed time orient the curve to have turning number \(+1\), set \(\kappa=2\pi/L\), and choose the zero-mean periodic lift \(\phi\) such that \(T=e^{i\alpha+i\kappa s+i\phi}\). Let \(a=51/100,\ x=\sqrt{d}\), and \(m=\|\phi\|_2/\sqrt L\). The twice-applied closure estimate, invariant under rescaling in this notation, gives \(m\le a x/(2\pi)\). In fact \(a^2>13/50\). Let \(S=(\pi^2/3-1)^{1/2}<38/25\).

In centered arclength Fourier coordinates the first position harmonic is a circle of radius \(|\widehat T_1|/\kappa\), and \(1-m^2/2\le|\widehat T_1|\le1\). The position remainder has sup norm at most \(Sm/\kappa\): integrate all nonzero tangent harmonics other than the first and use Cauchy–Schwarz, since their squared coefficients sum to at most \(m^2\). These bounds follow directly by comparison with \(T_0=e^{i\alpha+i\kappa s}\). For every unit direction \(e\),
\[
 \max \langle X-c,e\rangle\ge\frac{L}{2\pi}(1-m^2/2-Sm),\qquad
 \|X-c\|_\infty\le Lr,\quad r=\frac{1+Sm}{2\pi}.
\]
The outer estimate also improves the mobility estimate below. The ratio \(L/(2\pi R_E)=1+d/(4\pi^2)\) is retained in the lower support bound. [Fourier comparison for support](https://arxiv.org/html/2611.07242v1#S4)

## Centroid displacement in physical units

Let \(u=k-\kappa,\ H=k(X-c)+N,\ \Gamma_0=-iT_0/\kappa\). Then \(H=u(X-c)+\kappa(X-c-\Gamma_0)+(N-iT_0)\). Since \(X-c-\Gamma_0\) has mean zero, Wirtinger's inequality and \(|e^{i\phi}-1|\le|\phi|\) give
\[
 \|H\|_2\le Lr\sqrt{d/L}+2\|\phi\|_2
          \le (r+a/\pi)\sqrt{Ld}.
\]
Use the doubled-speed convention \(G=2k_{ss}+k^3,\ Y=\int G^2ds\). The centroid variation, dilation virial and energy identity are
\[
 Lc'=\int GH\,ds,\qquad \sqrt Y\ge 2\pi B/L^{3/2},\qquad R_E'=2\pi Y/B^2>0.
\]
They imply \(|c'|/R_E'\le(1+d/(4\pi^2))x(r+a/\pi)\). This ratio is also valid in the physical half-speed convention since both time derivatives acquire the same factor. [Variation formulas, Lemma 2.1](https://arxiv.org/html/2611.07242v1#S2)

## Uniform margins

For \(0\le x\le2\) one has \(m\le(41/500)x\) and \(1/40<1/(4\pi^2)<13/500\). The upper coefficient for mobility is at most \(4/5\); one may replace \(2\pi\) in the denominator of \(r\) by \(2(157/50)\), and similarly \(\pi\) by \(157/50\) in \(a/\pi\). For support first use \(1-m^2/2-Sm\ge1-x/8-17x^2/5000\), which stays positive. Multiplication by \(1+x^2/40\) gives a lower bound \(1-x/8+3x^2/200\ge81/100\). Thus, for each time \(t\), every direction has support at least \(81R_E(t)/100\) beyond \(c(t)\), while \(|c(t)-c(s)|\le(4/5)(R_E(t)-R_E(s))\). Changing the center to \(c(s)\) leaves directional margin at least \((4/5)R_E(s)+R_E(t)/100\). Separation of convex sets gives the claimed closed disk.

The independent Migration project verifies the scalar Fourier bootstrap, the uniform bounds on support and mobility and the inclusion of the closed disk from the two geometric inequalities. The Fourier and flow estimates transporting the initial sublevel to these inputs are written arguments. [Lean disk proof](../../Migration/DefectFourHull.lean)
