# A quadratic asymptotic for all ordinary crossings of primitive rotating expanders

Let \(h=m/d\) be in lowest terms on the [rotating branch](../IntegerRotatingWinding.md) near \(h_0=-1\). The signed tangent turning over one support period is measured in revolutions. Write \(N(h)\) for the number of *distinct image points* in a primitive closed traversal which have exactly two preimages and distinct tangent lines. There is a positive constant \(A_0\) determined by the single winding-one reference orbit. Along \(h=-1+1/d\),
\[
                      N(h)=A_0 d^2+O(d^{5/3}).
\]
Orientation reversal realizes turning number and centre winding \(n=d-1\), for every sufficiently large \(n\). The certified enclosure is \(10.09<A_0<14\). In particular, eventually these examples have more than \(10(n+1)^2\) distinct ordinary transverse double points. This counts intersections over the entire image. The [two-band formula](TwoAnnuli.md) gives an exact finite-\(d\) count in two smaller regions.

For any nearby reduced rational \(h\), the uniform estimate is \(N(h)=d^2 A(h)+O(d^{5/3})\) with \(A\) locally Lipschitz at \(-1\). Consequently \(N(h)/d^2\to A_0=A(-1)\) along *every* sequence of distinct such rationals approaching \(-1\). The error when replacing \(A(h)\) by \(A_0\) includes \(O(d^2|h+1|)\).

## The single-block geometric coefficient

The radius \(r=|X|\) has precisely 72 nondegenerate extrema per block, and stays above \(0.17\) on the reference orbit. All 72 critical radii differ. The [checker](density_geometry.py) takes every certified critical cell in the [whole-orbit enclosure](WholeOrbitFourier.md). If its initial radius and tangential support are \(r_j,q_j\), the critical value is within \(\delta (|q_j|+90\delta)/(r_j-\delta)\) of \(r_j\), where \(\delta=61/65536\), by \(r_s=q/r\) and the component speed bound. The 72 resulting intervals are strictly ordered. The Morse extrema and their order persist on the analytic branch, after shrinking its parameter interval.

Cut the support-phase circle at a critical point and take one lift of each of the 72 arms between successive extrema. Each has strictly monotone radius. On arm \(i\) let \(\alpha_i(r,h)\) be a continuous polar angle in revolutions; the curve avoids zero. On the overlap \(I_{ij}(h)\) of their open radius ranges set
\[
           A(h)=\sum_{i<j}\operatorname{Var}_{I_{ij}(h)}(\alpha_i-\alpha_j).
\]
An empty overlap contributes zero. Fixed changes of angle lift on an arm do not affect this quantity.

## Why the arms have no persistent alignment

At a nondegenerate radial extremum of positive radius \(r_e\), an adjacent arm has an analytic expansion in \(\sqrt{|r-r_e|}\) with nonzero linear coefficient. The two incident arms have opposite such coefficients of equal magnitude. Indeed arclength is an analytic function of the signed square root with nonzero derivative, and the polar angle has nonzero arclength derivative at that point because the unit tangent is perpendicular to the position. Possible endpoint lifts differ only by a constant.

On any nonempty common radius interval, two *different* arms have nonconstant angle difference. Otherwise continue the constant relation to the full overlap. At least one of its ends has just one of the two arms critical there. If both ends were shared, the two distinct edges of a simple cycle of length 72 would have both endpoints in common, since all critical radii differ. The uncancelled square-root term at the single critical end contradicts the relation.

Next fix three distinct arms with positive common overlap. Their two angle differences
\[
             Z(r)=(\alpha_j-\alpha_i,\alpha_k-\alpha_i)
\]
cannot trace part of a straight line. Such a line gives a nonzero linear relation between the three angles and a constant, with coefficient sum zero. Extend it by analyticity to the entire overlap. If only one arm is critical at one end, its square-root term forces its coefficient to vanish. The preceding two-arm argument rules out the remaining relation. In the other case, each end has two incident critical arms. At either end, the opposite square-root coefficients force the two corresponding coefficients of the relation to be equal. The two pairs at the two ends differ, by the same cyclic adjacency and distinct-critical-values argument. Thus all three coefficients are equal and their sum zero, contradicting nontriviality.

## Uniform counts for pairs, tangencies and higher multiplicity

For any pair or triple overlap with endpoints \(a(h),b(h)\), use the coordinate \(r=a+(b-a)\sin^2(\pi t/2)\), \(0\le t\le1\). Since the ordering of critical values remains strict, the endpoints follow fixed extrema analytically. Each restricted angle is jointly real analytic in \(t,h\) up to and across the two ends on suitable local extensions. At a critical end this substitution supplies the signed square root from the analytic Morse lemma; at a regular end this follows by ordinary analytic inversion. Thus \(A_{ij}(h)=\int_0^1|\partial_t(\alpha_i-\alpha_j)|\,dt\) is locally Lipschitz by bounded mixed derivatives.

A one-variable analytic function of \(t\) in this compact interval that is not identically zero at \(h_0\) has a uniformly bounded number of zeros for \(h\) close to \(h_0\). Around each zero a fixed finite-order derivative stays nonzero also for nearby \(h\); repeated Rolle bounds the number there. On the remaining compact set the function stays away from zero. This applies to each pair derivative and, for a triple, to the first component derivative of \(Z\) and to \(\det(Z',Z'')\). The latter is not identically zero, since otherwise the slope would be constant where the first component derivative is nonzero and the analytic curve would lie in a line. Only finitely many pairs and triples enter.

A point of a given positive radius on one arm has \(d\) distinct rotated copies in the primitive closed curve. Two arms give coincident copies precisely when their angle difference is in \(d^{-1}\mathbb Z\), since \(m,d\) are coprime. Each coincidence radius for that pair gives \(d\) unordered label pairs. On each monotone piece the number of attained grid levels differs from \(d\) times its angle variation by at most a constant. The finitely many piece boundaries, critical radii of the whole block and critical points of angle differences contribute \(O(d)\) label pairs in total. Away from those sets a pair is transverse by its nonzero derivative with respect to radius. The number of transverse unordered label pairs is therefore \(d^2 A(h)+O(d)\).

A third preimage requires two angle differences to lie simultaneously in \(d^{-1}\mathbb Z\). The above derivative and determinant bounds partition each \(Z\) into a uniformly bounded number of strictly convex or concave graphs over its first coordinate. Their arclengths are uniformly bounded, since they are integrals of uniformly bounded derivatives in the compact \(t\)-coordinate. On such a graph scaled by \(d\), successive lattice points in order of first coordinate have strictly monotone chord slopes. Their nonzero integer chord vectors are consequently distinct. For \(T=d^{1/3}\), at most \((2T+1)^2\) can have length at most \(T\), and at most \(Cd/T\) have length greater than \(T\), by the arclength bound. This proves \(O(d^{2/3})\) lattice hits per triple, including the finitely many division points. Each hit gives \(d\) rotated triples. Critical radii add \(O(d)\) because each half-open block has at most 144 labels of any given radius, and distinct rotations of a nonzero point are distinct.

Every point of multiplicity \(u\ge3\) accounts for at most \(3\binom u3\) unordered pairs, since \(\binom u2\le3\binom u3\). Deleting all these pairs costs \(O(d^{5/3})\). Every remaining transverse pair gives a different ordinary double point. This proves the global estimate.

## A numerical enclosure for the coefficient

The lower verifier samples rational radius levels \(j/4096\) on all 72 arms. At a bracketed level, unit speed gives the true polar angle error from the adjacent node as at most \(\delta/(2\pi(r_j-\delta))\) revolutions. The node angle is reconstructed from the Fourier antiderivative of curvature and the argument of \(q+ip\), with the [previous analytic transfer error](TwoAnnuli.md). Consecutive phases have unique consistent lifts since their true angular displacement is below \(0.01\) revolutions. Each inverse radius is bracketed by interval signs.

For an ordered sequence of angular-difference intervals, the least possible total variation gives a lower bound for the true variation. To compute it, keep the interval of final positions minimizing accumulated variation. If it meets the next interval retain their intersection; if they are separated add their distance and retain the closest point of the new interval. Inductively the least variation to any terminal value in the current interval equals the best value plus its distance to the retained interval. The calculation uses outward-rounded integer endpoints and sums over all arm pairs. It yields \(A_0\ge10.09779369\).

For an independent [upper bound](density_upper.py), at radius \(r\) let \(n(r)\) count the arms meeting that circle. The triangle inequality charges the variation of each arm at most \(n(r)-1\) times. For each arclength cell the checker finds all arm ranges that could meet it, using the critical cells for the two ends. On that cell it bounds \(|\psi_s|=|p|/r^2\) in radians, by unit speed and \(|p_s|=|kq|\le \|k\|_\infty r\). Summing the resulting upper bounds gives \(A_0<14\).

The full-image asymptotic is a written proof using rigorously bounded computations on the reference orbit. The [Lean counting theorem](../ArmMultiplicity/OuterArmMultiplicity.md) covers the conditional two-arm lower bound in an actual primitive period. The global asymptotic and the full existence argument on the rotating branch still have steps outside Lean.
