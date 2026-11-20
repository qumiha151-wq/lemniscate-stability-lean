# Alternating groups of large-turning curvature arcs

Work in the RMS normalization of [the critical inflection-density estimate](CriticalInflectionDensity.md), so \(\int_0^P k^2=P\), \(f=k''+k^3/2\), \(D=\int f^2\), and \(d=D/P\). Each component of \(\{k\ne0\}\) has turning \(\int_I|k|\,ds\). Retain the components with turning greater than \(1/4\), in their cyclic order, and group consecutive retained components of the same sign. Let \(n\) denote the number of resulting cyclic groups, taking \(n=1\) for an empty list or a list of only one sign. There are finitely many retained components since their turning sums to at most \(\int|k|\). Then
\[
       \sqrt d\ \ge\ \tfrac12-C n^{3/2}/P
\]
for a universal constant \(C\). Grouping discards arbitrarily many same-sign large leaves separated by small opposite-sign dips. The example with no curvature zeros follows directly by integrating \(f\) and applying Hölder.

## Small-angle leaves with a high peak

Set \(\delta=1/4\). On a complete leaf \(I\) with \(A_I=\int_I w\le\delta\), \(w=|k|\), let \(M=\max_I w>0\). Choose a maximum and let \(J\) be its component of \(\{w>M/2\}\), of length \(\ell\le2\delta/M\). Both its endpoints have value \(M/2\). Cauchy–Schwarz on the rise and the fall gives \(\int_J |w'|^2\ge M^2/\ell\). Multiplying the actual equation \(w''+w^3/2=(\operatorname{sign}k)f\) by \(w-M/2\) on \(J\) gives
\[
 \int_J|f|\ \ge\ 2M/\ell-\ell M^3/2
              \ \ge\ (1-\delta^2)M^2/\delta . \tag{1}
\]
If \(M\ge1/2\), then \(\ell/2\le\delta/M\le8\delta^2 M^2/\delta\). Thus Cauchy–Schwarz on \(J\) implies
\[
 R_I:=\int_I(|f|-1/2)^2
 \ \ge\ (1-9\delta^2)^2 M^5/(2\delta^3),\qquad
 \int_I w^3\le\delta M^2\le \frac{16}{49}R_I. \tag{2}
\]

## Summing the tents across groups

Choose the boundary between two consecutive opposite groups at a curvature zero separating their retained leaves, e.g. the far endpoint of the final retained leaf of the first group. If the list has at most one sign, cut the circle at any zero. On each resulting interval \(I\), choose its group sign \(\sigma\) (arbitrary for an empty list). Every leaf of the opposite sign is a complete small leaf. Let \(\phi=\min(1,s-\inf I,\sup I-s)\) and \(u=\sigma k\). Set \(A=\max(1,\sqrt{\max(k'^2+k^4/4)^{1/2}})\), so \(|k|\le2A\). The integration by parts in the preceding estimate gives \(\int_I\phi u''\ge-4A\), since the two endpoint values are zero and downward slope jumps have total size two. On \(u\ge0\) the original ramp and plateau estimates give \(3u^2/2-\phi u^3\le1/2\) away from the ramps, and an integrated excess at most \(16A\) on the two ramps combined. For \(-1/2\le u\le0\), \(3u^2/2-\phi u^3\le1/2\) everywhere. For \(u=-w<-1/2\), one instead uses
\[
 3w^2/2+\phi w^3-1/2\le2w^3,
\]
because \((w-1)^2(w+1/2)\ge0\). Each such point lies on a complete wrong-sign leaf with peak at least \(1/2\), which can be charged by (2). Consequently
\[
 \frac32\int_I k^2\le 2\int_I|f|+\frac{|I|}2+24 A
                    +\frac{32}{49}\sum_{\text{charged leaves in }I}R_I^{\rm leaf}.
\]
In the case \(D<P/4\), write \(X=P/2-\int|f|\) and \(R=\int(|f|-1/2)^2\). Then \(0\le R\le X\), and summing the disjoint charges gives
\[
       X\le 12n A+(16/49)R,\qquad R\le X\le C n A. \tag{3}
\]

## The normalized stress window

For \(A\ge2\), start at a maximum of the stress and set \(K(y)=k(s_0+y/A)/A\), \(g=K''+K^3/2\). The stress amplitude at the initial point is one. Let \(p=200(n+3)\), and first suppose \(p/A\le P\). We claim \(\int_0^p|g|>1/4\). Otherwise \(3/4\le(K'^2+K^4/4)^{1/2}\le5/4\), hence \(|K|,|K'|\le2\). The angular mass of every complete leaf is invariant under this rescaling. By (1) any complete small leaf with \(\max|K|\ge1/3\) would consume at least \(5/12\) of forcing, exceeding the available \(1/4\).

Intersect the original cyclic groups with the window. This initially makes at most \(n+1\) pieces. At most two wrong-sign leaves meet a window endpoint and are truncated there. If present, separate each truncated piece and assign its own sign. If the entire window lies in a single sign leaf, use that one piece alone. The resulting at most \(n+3\) pieces satisfy \(\sigma K\ge-1/3\). Pointwise \(|K|^3\le\sigma K^3+2/27\). Integrate \(K''=g-K^3/2\) on each piece to get
\[
 \int_0^p|K|^3\le2\int_0^p|g|+8(n+3)+(2/27)p.
\]
On the other hand \((KK')'=K'^2+K^4/4-3K^4/4+Kg\) gives \((3/4)\int K^4\ge9p/16-8-1/2\). Using \(\int K^4\le2\int |K|^3\) contradicts the chosen \(p\).

Returning to the unscaled RMS coordinates, (3) gives
\[
 A^2/4<\int_{s_0}^{s_0+p/A}|f|
    \le p/(2A)+\sqrt{pR/A}\le Cn .
\]
If \(p/A>P\), then \(A<p/P\), which suffices whenever \(P\ge n^{3/2}\). For \(P<n^{3/2}\) the claimed estimate follows from \(d\ge0\) after increasing \(C\). This proves \(\sqrt d\ge\int|f|/P\ge1/2-Cn^{3/2}/P\).

In physical variables \(P=\sqrt{2EL}\). All conclusions from the scalar time comparison for the critical inflection density therefore hold with this grouped count. In particular a trajectory violating \(L(t)=O(t^{1/4+\varepsilon})\) for some \(\varepsilon>0\) needs a late sequence with \(EL\to\infty\) and at least \(c(EL)^{1/3}\) alternating groups. A positive limiting energy also forces such a sequence. The matching rectangular packets in the cited construction contain order \(n\) interior alternating lobes with turning close to \(\pi\), so the order of the single-slice dependence persists.

## What a dissipation cost per birth would need

Even if one could allocate a disjoint genuine birth to every new alternating group, a lower bound comparable to inverse RMS length per group would not by itself exclude positive limiting energy. On lengths \(L_j=2^jL_0\) with \(E_j\) bounded above and below, the necessary \(n_j\) has order \(L_j^{1/3}\), whereas inverse RMS length has order \(L_j^{-1/2}\). The resulting series \(\sum_j L_j^{-1/6}\) converges. Even under the stronger bookkeeping assumption of \(c n_j\) new groups at each successive length doubling, these lower bounds are compatible with finite total dissipation. This is a limitation of the numerical exponents in the proposed inference, and supplies no geometric trajectory with positive limiting energy. The actual fixed-angle barriers must charge the *individual* curvature scales of the macroscopic groups, or supply a stronger count, to yield a divergent sum.

## A necessary sum of individual peak curvatures at low dissipation

Let \(M_i\) be the largest peak \(\max_I |k|\) among the retained leaves in group \(i\), with value zero for an empty group. There are absolute constants \(c_*,d_*>0\) such that on every RMS-normalized slice with \(P\ge400\),
\[
                   d\le d_*\quad\Longrightarrow\quad \sum_i M_i\ge c_*P. \tag{4}
\]
Thus one peak per alternating group suffices. A train of large positive leaves separated only by small negative gaps contributes the largest of its positive peaks once.

Indeed the earlier tent proof on group \(i\) uses only \(A_i=\max(1,\sup_I(\sigma k)_+)\) for the ramp and the downward slope jumps. Its endpoints remain zeros, and the opposite high peaks were already covered by (2). We therefore have \(12\sum_i A_i\ge X-(16/49)R\ge(33/49)X\). If \(d\le1/16\), then \(X\ge P/4\), and in particular \(\sum_i A_i\ge P/100\).

For every complete small leaf, irrespective of height, (1), Cauchy–Schwarz and \(\ell\le2\delta/M\) give
\[
 M^5\le C_0\int_I f^2,\qquad C_0=2\delta^3/(1-\delta^2)^2.
\]
Let \(s_i\) be the supremum of peaks on small leaves of the chosen group sign, or zero for an empty collection. Taking one such leaf from each group and then passing to the supremum gives \(\sum_i s_i^5\le C_0D\). Since every retained leaf has angular mass greater than \(\delta\), \(n\le4P\) when \(P\ge1\), including the empty-list convention. Hölder yields \(\sum_i s_i\le 4^{4/5}(C_0d)^{1/5}P\). Choose \(d_*\le1/16\) so this last coefficient is at most \(1/400\).

When \(n\le P/400\), the upper bound \(A_i\le1+M_i+s_i\) now gives \(\sum_i M_i\ge P/200\). When \(n>P/400\), the hypotheses \(P\ge400\) and \(n>1\) ensure that every group has a retained leaf. If the group lengths are \(\ell_i\), each \(M_i\ell_i\ge\delta\). Consequently \(\sum_i M_i\ge\delta n^2/P\ge P/640000\). This proves (4) with \(c_*=1/640000\).

For a genuine flow, multiply physical curvature by \(\lambda_R=\sqrt{L/(2E)}\) to reach the RMS normalization, so \(P=L/\lambda_R\) and \(P/\lambda_R=2E\). At times satisfying the assumptions of (4), the sum of the *physical* selected peaks is thus at least \(2c_*E\). On the hypothetical branch \(E_\infty>0\), the length tends to infinity. Indeed if infinitely many unit time windows began at lengths bounded by \(K\), the time secant estimate would bound their lengths by \(K+E(0)\), and the virial inequality \(\mathcal D\ge4\pi^2 E^2/L^3\) would contradict finite total dissipation on a disjoint subsequence of those windows. Thus eventually \(P\ge400\). In the divergent clock \(d\zeta=E^2L^{-2}dt\), the identity \(\int d\,d\zeta=\frac18\log(E(0)/E_\infty)<\infty\) shows that (4) holds except on a set of finite \(\zeta\)-measure. Divergence follows from \(E\ge E_\infty\) and the secant bound \(L(t)=O(\sqrt{1+t})\).

This identifies the time-dependent estimate a birth argument would need. If one could charge a fixed fraction of these selected *terminal peak values* to physical dissipation in disjoint late time windows with bounded multiplicity, the lower bound \(2c_*E_\infty\) would contradict finite tail dissipation. A newly formed cell can attain a large turning while broad and weak, and only later gain peak curvature after its turning has exceeded the small-angle threshold. The angular count and (4) identify substantial terminal values, but neither relates them to the curvature scale when those groups first acquired their angular mass. The actual small-angle and bounded-width estimates require this connection on their formation intervals.
