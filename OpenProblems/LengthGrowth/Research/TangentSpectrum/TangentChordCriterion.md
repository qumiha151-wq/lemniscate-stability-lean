# A physical tangent-increment criterion for fourth-root length growth

Let \(X\) be a smooth closed planar free elastic flow in the paper's time convention. At time \(t\), let \(T_t(u)\) be the actual unit tangent in arclength coordinates divided by length, so \(u\) has period one. Put \(E=\frac12\int k^2\,ds,\ U=EL\). Define
\[
 Q(t,h)=\int_0^1 |T_t(u+h)-T_t(u)|^4\,du.
\]
The quantity is independent of the starting arclength label, the orientation and rigid motions. The bound \(L(t)=O(t^{1/4})\) is equivalent to
\[
 \lim_{h\downarrow0}\ \sup_{t\ge0} Q(t,h)/h=0.
\]
Moreover, if the length bound fails, there are arbitrarily late record times with \(U(t)\) arbitrarily large. At **every** such positive record the particular lag \(h=1/(64U(t)^{2/3})\) satisfies \(Q(t,h)/h\ge 2^{-22}\). Thus a test using tangent directions at pairs of points can detect a necessary feature of a counterexample.

## Proof

Write \(\omega_n=2\pi n,\ c_n=\widehat T_t(n)\), and \(M_j=\sum_n|\omega_n|^j|c_n|^2\). The physical moment identities give \(M_2=2U\) at all times and \(M_4\le1024 U^{7/3}\) at positive records. [Physical record estimate](../../LengthGrowth/ActualFlow/TangentFlowRecord.lean)

With \(D_2=\int_0^1 |T_t(u+h)-T_t(u)|^2du\), Parseval identifies \(D_2\) with the sum weighted by \(|e^{i\omega_n h}-1|^2\). The elementary inequalities
\[
 x^2-4x^4\le 4|e^{ix}-1|^2,\qquad |e^{ix}-1|\le |x|
\]
hold on the real line. For the lower bound use \(|e^{ix}-1-ix|\le x^2\) on \(|x|\le1/2\), and the nonpositivity of the left side on the complement. Consequently \(4D_2\ge h^2 M_2-4h^4 M_4\) and \(D_2\le h^2 M_2\). Cauchy–Schwarz gives \(D_2^2\le Q\), while \(|T(u+h)-T(u)|\le2\) gives \(Q\le4D_2\).

At the specified lag the lower estimate becomes \(D_2\ge h^2U/4\), giving \(Q/h\ge h^3 U^2/16=2^{-22}\). If the fourth-root upper bound holds, \(U\) is uniformly bounded, hence \(Q/h\le8h\sup_t U(t)\). If it fails, there are arbitrarily late record values \(U\to\infty\), and their lags decrease to zero. These two implications prove the equivalence.

## A geometric sufficient condition

For \(1\le p<4\), suppose a time tail of the unit tangents has uniformly bounded cyclic \(p\)-variation. Here the bound means that \(\sum_j|T(u_{j+1})-T(u_j)|^p\le V\) for every cyclic arclength partition. This condition permits unlimited total turning when \(p>1\). It implies fourth-root length growth.

Indeed, for \(0<h\le1/2\) integrate over starting labels the sum of the first \(\lfloor1/h\rfloor\) increments at spacing \(h\). They are consecutive increments of a cyclic partition, so \(\int|\Delta_h T|^p\le 2Vh\). For \(2\le p<4\), Hölder gives \(D_2^2/h\le(2V)^{4/p}h^{4/p-1}\to0\); for \(1\le p<2\), the uniform bound by two on each increment gives \(D_2^2/h\le 2^{6-2p}V^2 h\to0\). Either estimate contradicts the lower bound for \(D_2^2/h\) at the escaping records.

The independent LengthGrowth project checks the physical fourth-moment integration, the exact lag lower bound at each positive record, and both directions of the criterion expressed using the actual real supremum over all nonnegative times. The cyclic variation consequence above is a written corollary. [Record inequality](../../LengthGrowth/ActualFlow/TangentPhysicalIncrement.lean) · [Supremum limit and equivalence](../../LengthGrowth/ActualFlow/TangentIncrementCriterion.lean)

Whether arbitrary closed free elastic flows satisfy the vanishing tangent-increment criterion remains open.

