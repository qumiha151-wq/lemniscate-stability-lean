# Pure expanding profiles when the stress can vanish

Let \(X(s)\) be any smooth regular closed planar pure expanding profile,
parametrised by arclength about its actual expansion centre. Dilate to set
the positive dilation coefficient to one. Thus
\[
 T=X_s,\quad N=JT,\quad T_s=kN,\quad
 F=k_{ss}+\tfrac12k^3=-X\cdot N,\quad
 W=\tfrac12k^2T+k_s N,\quad W_s=-(X\cdot N)N .
\]
Write \(S=|W|,\ H=\max S,\ R=\max |X|\), with maxima over the full
closed curve. Nonstraightness gives \(H>0\). The following conclusions
do not require a lower bound for \(S\), even pointwise on the
individual curves. Periods and turning numbers can vary.

1. There is a numerical constant \(C<\infty\) such that \(R\le C\sqrt H\)
   for every such profile. In an arbitrary dilation normalisation this
   is \(\lambda R^2\le C^2 H\).
2. For any sequence with \(H_j\longrightarrow\infty\),
   \(\operatorname{dist}(0,\operatorname{conv}X_j)/\sqrt{H_j}\to0\).
   If each curve is strictly separated from its centre, take any unit
   separating normal \(e_j\) with \(X_j\cdot e_j>0\), and *any* point
   \(s_j\) where \(S_j(s_j)=H_j\). Then
   \[
   |X_j(s_j)|/\sqrt{H_j}\to0,\qquad
   e_j\cdot W_j(s_j)/H_j\to0.
   \]
   On a subsequence on which \(W_j(s_j)/H_j\to u\), the rescaled
   limiting curve contains the full straight segment
   \([-\sqrt{3\mu}\,u,\sqrt{3\mu}\,u]\), where \(\mu\) is specified below.
3. The maximum radius has the exact high-stress asymptotic
   \(R/\sqrt H\to\sqrt{3\mu}\). No nondegeneracy assumption is needed.
4. On the set where the limiting rescaled stress vanishes, at almost
   every point with limiting position \(Z\ne0\), the weak limit of the
   tangents is parallel to \(Z\). In particular a straight segment is
   a genuine degeneracy of this argument. It gives no positive
   two-dimensional inradius and does not decide an unscaled strict
   separation tending to zero in the units of (2).

## Two facts about the constant-forcing limit

**Lemma 1.** A unit-speed complete solution on the whole arclength line
with \(F=-A e\cdot N\), \(A>0\), \(|e|=1\), and bounded stress \(W\),
is a straight line parallel to \(e\).

Indeed \((W\cdot e)'=-A(e\cdot N)^2\). The integral of
\((e\cdot N)^2\) over the line is finite, and \(N\) is Lipschitz
because \(k\) is bounded. Hence \(e\cdot N\to0\) at both ends.
At each end \(T\) tends to a single one of \(e,-e\) by continuity.
The second derivative \(T''=k_sN-k^2T\) is bounded, so \(T'\to0\)
at both ends. Here one can apply the difference-quotient estimate
to each component of \(T\), taking first a fixed small step and then
sending it to zero. Thus \(k\to0\), and \(k_s\to0\) by the same estimate
since \(k_{ss}=-k^3/2-A e\cdot N\) is bounded. Therefore \(W\) tends
to zero at both ends. Monotonicity of \(W\cdot e\) now forces
\(e\cdot N\equiv0\).

**Lemma 2 (fast phases).** Let \(D_j,A_j>0\), and introduce the
coordinate \(\zeta=(s-s_j)D_j/A_j\). Suppose the available
\(\zeta\)-intervals exhaust the real line, \(|w_j|=|W_j|/A_j\) is
uniformly bounded, \(X_j/D_j\to d\) locally uniformly for a nonzero
constant vector \(d\), and \(A_j^{3/2}/D_j\to\infty\). Then every
locally uniform limit of \(w_j\) is zero.

The exact equation is
\[
 (w_j)_\zeta=-N_jN_j^\top(X_j/D_j).
\]
It implies local equicontinuity. Write \(w\) for a subsequential
limit. On any closed interval where \(|w|>0\), set
\(u_j=w_j/|w_j|\), \(q_j=k_j/\sqrt{S_j}\), \(v_j=(k_j)_s/S_j\).
The pair \((q_j,v_j)\) lies on \(q^4/4+v^2=1\). In the frame
\((u_j,Ju_j)\), \(T_j=(q_j^2/2,-v_j)\) and \(N_j=(v_j,q_j^2/2)\).
Writing \(G=(v,-q^3/2)\), \(B=(-qv/2,1-v^2)\), the arclength equation is
\[
 (q,v)_s=\sqrt S\,G+(F/S)B .
\]
In \(\zeta\) time its leading coefficient is
\((A_j^{3/2}/D_j)\sqrt{|w_j|}\to\infty\); its remainder coefficient
\((F_j/D_j)/|w_j|\) is bounded on the interval. The reciprocal of the
leading coefficient and its first derivative are uniformly
\(O(D_j/A_j^{3/2})\), by the Lipschitz bound for \(w_j\). Each smooth
zero-mean function on the oscillator orbit is the derivative of a
smooth periodic primitive along \(G\), since \(G\) never vanishes on
the compact orbit. Integration by parts against this reciprocal
therefore makes its integral against any uniformly Lipschitz bounded
multiplier tend to zero.

The oscillator means are \(\langle v\rangle=\langle vq^2\rangle=0\),
\(\langle v^2\rangle=2/3\), \(\langle q^4/4\rangle=1/3\).
They follow from periodic derivatives of \(q,q^3,qv\) and the
level identity. Replacing \(X_j/D_j\) by its uniform limit in the
integral and averaging gives, on the open set \(w\ne0\),
\[
 w'=-\tfrac13(I+u u^\top)d,\qquad u=w/|w|.
\]
Thus \((w\cdot d)'\le-|d|^2/3\) on each nonzero component.
A component unbounded in either time direction contradicts bounded
\(w\). A bounded component has zero values at both endpoints and
violates the same strict decrease. This proves the lemma without
using any angular frame on the zero set.

## The radius estimate

Suppose \(R_j/\sqrt{H_j}\to\infty\). At a maximum of radius,
\(0\ge (|X|^2/2)_{ss}=1+k(X\cdot N)\); hence
\(R_j\sqrt{2H_j}\ge1\). These two bounds imply \(R_j\to\infty\).
Extend the arclength solutions periodically to the entire line,
choosing a maximum of radius at \(s=0\).

We claim \(S_j=O(R_j^{2/3})\) throughout \(|s|\le R_j/4\).
Otherwise, pass to a subsequence with a point in that interval where
\(A_j^{\mathrm{init}}/R_j^{2/3}\to\infty\), taking \(A=S_j(s)\).
Choose \(L_j\to\infty\) so slowly that \(L_j H_j/R_j^2\to0\).
If \(|W_j|\le2A\) throughout the interval \(|s'-s|\le L_j A/R_j\),
stop. Otherwise move to a point in the interval with stress greater
than \(2A\) and repeat with the new stress. For each \(j\) the process
stops since the stress is bounded by \(H_j\). The total distance moved
is at most \(2L_j H_j/R_j=o(R_j)\), by the geometric growth of the
successive stresses.

At the final point \(s_j\) denote its stress by \(A_j\).
The bound \(|s_j|\le R_j/4+o(R_j)\) implies
\(|X_j(s_j)|/R_j\ge 3/4-o(1)\). After selecting a subsequence,
\(X_j(s_j)/R_j\to d\ne0\). With \(D_j=R_j\), the change of \(X_j/D_j\)
on a fixed \(\zeta\)-interval is \(O(A_j/R_j^2)=o(1)\) by unit speed.
The stopping condition gives \(|w_j|\le2\) on \([-L_j,L_j]\).
Finally \(A_j^{3/2}/R_j\to\infty\) by the initial choice. Lemma 2
forces \(w_j\to0\) along the extracted subsequence, contradicting
\(|w_j(0)|=1\). This proves the claim.

At the maximum of radius now take the inner scale \(\eta=R_j^{1/3}s\).
Put \(K=k_j/R_j^{1/3}\), \(V=(k_j)_s/R_j^{2/3}\), \(Z=X_j/R_j\).
The claim bounds \(K,V\) uniformly on intervals exhausting the line.
The equations in \(\eta\) are
\[
 K'=V,\quad V'=-K^3/2-Z\cdot N,\quad T'=KN,\quad Z'=R_j^{-4/3}T.
\]
After extraction they give an entire true constant-forcing limit
with \(Z\equiv e\) a unit vector and bounded stress. The initial
tangent is perpendicular to \(e\), by the maximum-radius condition.
This contradicts Lemma 1, proving (1).

## The outer limit with stress zeros

For \(H_j\to\infty\) use \(\ell=(s-s_j)/\sqrt{H_j}\),
\(Z_j=X_j/\sqrt{H_j}\), \(w_j=W_j/H_j\), with
\(S_j(s_j)=H_j\). The entire extended trajectories satisfy
\[
 (Z_j)'=T_j,\qquad (w_j)'=-N_jN_j^\top Z_j,\qquad |w_j|\le1 .
\]
The radius theorem bounds \(Z_j\) globally. Compactness gives local
uniform limits \(Z,w\) on the full line, with \(|w(0)|=1\). On any
closed interval in the open set \(w\ne0\) apply the averaging argument
of Lemma 2 with \(A_j=H_j,D_j=\sqrt{H_j}\); its leading frequency is
\(H_j\sqrt{|w_j|}\). The coefficient \(Z_j\) is now a uniformly
Lipschitz multiplier. With \(\mu=\langle q^2/2\rangle>0\) the equations
become
\[
 Z'=\mu u,\qquad w'=-\tfrac13(I+uu^\top)Z,\qquad u=w/|w|.
\]
On the nonzero component through zero clock time put
\(P=w/\sqrt{|w|}\), \(d\tau=d\ell/\sqrt{|w|}\). The equations there are
\(\dot Z=\mu P,\ \dot P=-Z/3\), so \(Z\) parametrises a centred ellipse
or a line segment. Here are the continuation details. If \(Z(0)\)
and \(P(0)\) are linearly independent, the explicit harmonic solution
has \(|P|\) bounded away from zero. A finite endpoint in \(\ell\) would
then extend in \(\tau\) and preserve nonzero stress, contradicting
maximality of the component. Also \(d\tau/d\ell\ge1\); hence the
entire ellipse is realised in the compact-open rescaled limit.
It includes points on both sides of every line through the origin.

If instead \(Z(0),P(0)\) are collinear, \(|P(0)|=1\) is an interior
maximum of \(|P|\). Thus \(0=(|P|^2)^{\boldsymbol{\cdot}}(0)
=-2P(0)\cdot Z(0)/3\) and \(Z(0)=0\). Writing
\(\omega=\sqrt{\mu/3}\), the explicit solution is
\[
 P=P(0)\cos(\omega\tau),\qquad
 Z=\sqrt{3\mu}\,P(0)\sin(\omega\tau),\qquad
 |\tau|<\pi/(2\omega).
\]
All of this open interval belongs to the component, since on any
smaller compact subinterval \(|P|>0\) permits continuation as above.
The \(\ell\) times of the endpoints are finite, and continuity includes
the endpoints in the rescaled image. No continuation through a zero
of the frame is being presumed.

For strictly separated profiles choose any separating \(e_j\), pass
to a convergent subsequence, and take limits in \(e_j\cdot Z_j>0\).
The limiting image lies in one closed half-plane through zero.
This excludes the nondegenerate ellipse. The segment then forces
\(Z(0)=0\), \(e\cdot P(0)=0\). The same compactness argument on any
subsequence proves (2). In particular the scaled distance is bounded
above by the distance to the selected stress-maximum point. Profiles
whose hull already contains the centre have zero distance.

To see the residual zero-set equation pass on compact intervals to
the weak-* limit \(A\) of \(N_jN_j^\top\). This is a positive
semidefinite symmetric matrix of trace one almost everywhere,
and \(w'=-AZ\). A Lipschitz function has derivative zero almost
everywhere on its zero set. Thus \(AZ=0\) almost everywhere there.
On portions where \(Z\ne0\), test the weak convergence against the
bounded measurable projection onto \(Z/|Z|\), restricted to the
zero set. This gives local \(L^2\) convergence of
\(N_j\cdot Z/|Z|\) to zero on that set. The orthogonal component of
\(T_j\) has the same absolute value, so \(Z'\) is parallel to \(Z\)
almost everywhere there. This conclusion imposes no sign on the
residual transverse displacement of the unscaled curves.

These conclusions concern pure homothetic profiles. They do not
exclude profiles whose strictly separating distance is positive but
\(o(\sqrt H)\), nor do they prove common convex-hull intersection
for general time-dependent free elastic flow. The compactness and
averaging arguments in this note are analytic proofs.

## Interior of a zero-stress layer

The a.e. constraint strengthens on any connected open interval \(I\)
where \(w\equiv0\) and \(Z\) never vanishes. Throughout such an
interval \(Z\) follows a straight radial line at speed exactly one,
with a single choice of orientation. On every compact subinterval,
\[
 \frac{S_j}{H_j^{1/3}}\longrightarrow0,\qquad
 T_j\cdot J\frac{Z}{|Z|}\longrightarrow0
\]
uniformly in the outer variable \(\ell\). Thus an interior zero layer
cannot itself carry a transverse change of direction, stop, or reverse
while its limiting position is nonzero.

To prove this, slightly enlarge the chosen compact subinterval,
remaining inside \(I\). There \(S_j=o(H_j)\) uniformly and
\(0<c\le |X_j|/\sqrt{H_j}\le C\). If at interior points
\(S_j/H_j^{1/3}\) were unbounded, repeat the doubling argument in the
radius proof, now with \(D_j=\sqrt{H_j}\) and the local maximum
\(H_j^{\rm loc}=o(H_j)\) on the larger interval. Choose
\(L_j\to\infty\) with \(L_jH_j^{\rm loc}/H_j\to0\). The total
physical arclength moved in the doubling selection, including the
last verification window, is \(O(L_j H_j^{\rm loc}/\sqrt{H_j})
=o(\sqrt{H_j})\). Hence all selected intervals fit inside the fixed
larger outer interval. The final stress \(A_j\) has
\(A_j^{3/2}/D_j\to\infty\); the change of \(X_j/D_j\) on fixed
\(\zeta\)-intervals is \(O(A_j/H_j)=o(1)\). Lemma 2 again
contradicts unit normalised stress at the selected point.
Consequently \(S_j=O(H_j^{1/3})\) locally uniformly inside \(I\).

At any interior sequence of points, now rescale arclength by
\(D_j^{1/3}=H_j^{1/6}\), curvature by its reciprocal, and stress
by \(D_j^{-2/3}=H_j^{-1/3}\). The upper bound just obtained applies
on inner intervals exhausting the real line, and \(X_j/D_j\) tends
locally uniformly to a nonzero constant along a subsequence.
Lemma 1 forces the limit to be a parallel straight line of zero
stress. Subsequence contradiction gives both uniform conclusions
displayed above. On connected compact subintervals, continuous
alignment forces a spatially constant sign for the tangent projection
for each large \(j\). Passing to a subsequence and using \(Z_j'=T_j\)
gives \(Z'=\pm Z/|Z|\) with constant sign. The signs agree on
overlaps because \(Z\ne0\) and \(Z\) is already a fixed limit, which
proves the assertion on \(I\).

This argument uses both a larger zero interval and a positive lower
bound for \(|Z|\) on each compact subinterval. It does not extend the
orientation statement across an isolated zero of \(w\), or across
an endpoint adjoining an oscillatory component.

## Exact asymptotic maximum radius

All the outer compactness, averaging, and interior zero-layer results
hold with any base points \(s_j\); only the assertion \(|w(0)|=1\)
required a stress maximiser. Set \(r_*=\sqrt{3\mu}\). On any component
where \(w\ne0\), a nondegenerate harmonic ellipse is realised on the
entire harmonic time line. In the linearly dependent case the maximal
open harmonic time interval is a full interval between consecutive
zeros of \(P\). Indeed the solution can extend in physical time up to
each such zero because \(d\ell/d\tau=|P|\), while it cannot meet a
finite component endpoint where \(P\ne0\). The integral of \(|P|\)
over a finite harmonic interval is finite, so no zero at finite
harmonic time represents a physical time at infinity.

On an entire ellipse the quadrature identity
\(Z(\tau+\pi/(2\omega))=r_*P(\tau)\) bounds \(|Z|\) by \(r_*\),
since \(|P|\le1\). On a linearly dependent full half-period the same
bound follows from the sinusoidal amplitudes: \(\max |Z|=
r_*\max |P|\), including the values at its two zero-stress endpoints.
Therefore \(|Z|\le r_*\) everywhere on the nonzero stress set.
Any component of \(\{|Z|>r_*\}\) now has \(w=0\) and \(Z\ne0\)
on its entire interior. Its radius is affine of slope \(+1\) or \(-1\)
by the preceding section. A bounded component would have radius \(r_*\)
at both ends, and an unbounded component contradicts either the lower
bound \(r_*\) or global boundedness of \(|Z|\). Thus \(|Z|\le r_*\)
everywhere. Base the limit at points achieving \(R_j\). Applying this
conclusion to each convergent subsequence proves
\(\limsup R_j/\sqrt{H_j}\le r_*\).

For the opposite bound base the limit at points of maximum stress.
Their nonzero-stress component has \(|P(0)|=1\). A quarter harmonic
period away it attains \(|Z|=r_*\), at an included endpoint in the
linearly dependent case. Uniform convergence on the corresponding
fixed compact physical interval supplies
\(\liminf R_j/\sqrt{H_j}\ge r_*\). Combining the bounds proves (3).

For a strictly separated sequence with separating directions \(e_j\to e\),
the complete rescaled images in fact converge in Hausdorff distance to
the segment of radius \(r_*\) on \(e^\perp\). Every outer limit, based at
arbitrary points, lies in \(Z\cdot e\ge0\). Thus every nonzero-stress
component is a full linearly degenerate half-period along \(e^\perp\).
On any component of \(\{Z\cdot e>0\}\) the stress must vanish; the unit
radial line there has height affine with nonzero slope. This cannot
have zero height at both finite ends or remain bounded and positive on
an infinite end. Thus \(Z\cdot e=0\) for every such limit. Choosing
base points maximising the distance from the segment shows uniform
upper inclusion using the radius bound. The peak-based limit includes
the full segment by the explicit half-period above, giving the reverse
inclusion by compactness. This shape conclusion still allows a
subleading, strictly positive offset in physical units.
