# Arbitrarily many transverse double points on primitive zero-turn expanders

**Theorem.** For every positive integer \(n\), every sufficiently large centre marker \(b\) in the matched family of closed zero-turn free-elastic expanders gives at least \(2n\) distinct ordinary transverse double points on its primitive traversal. Each such point has exactly two parameter preimages. There are at least \(n\) on the positive ray of the seam axis and \(n\) on the opposite ray. In particular, the number of transverse double points tends to infinity along this family.

## Geometric data of the family

Normalize the dilation coefficient to one. Take \(X(0)=0,\ T(0)=e_x,\ k(0)=0,\ k_s(0)=b>0\), with \(N=JT,\ T_s=kN\) and \(k_{ss}+k^3/2=-X\cdot N\). The matched quarter ends at \(s_*=s_*(b)\) with \(X(s_*)\ne0,\ X(s_*)\cdot T(s_*)=k_s(s_*)=0\). Let \(e_b=X(s_*)/|X(s_*)|\) and let \(S_b\) reflect across \(\mathbb R e_b\). The second quarter is given by \(X(2s_*-s)=S_bX(s)\). Central inversion supplies the other half of the image. For large matched \(b\), the period \(4s_*\) is primitive, \(s_*/\sqrt b\to\tau_*>0\), and \(e_b\to e_y\).

We use one further estimate from the construction. On an initial interval \(0\le s/\sqrt b\le B<\tau_*\), fixed sufficiently close to \(\tau_*\), one has
\[
 \frac{X(s)}{\sqrt b}=\gamma\,\tau e_y+O_B(b^{-1}),\qquad \tau=\frac{s}{\sqrt b},
\]
where \(\gamma=P^{-1}\int_0^P U^2/2>0\) is a constant, with the oscillator \(U\) and period \(P\) defined below. Multiplying the estimate by \(b\) gives \(\gamma\sqrt b\,s\le |\sqrt b X(s)|+C_B\) throughout this interval. From \(B\) to the seam, \(|X|/\sqrt b\) is bounded below by a positive constant. Indeed the section and seam are at slow time tending to \(\tau_*\), the former with \(X/\sqrt b\to z_* e_y\), \(z_*>0\), and the slow-time position has speed one. Thus every first-quarter label with \(|\sqrt b X|\le C\) has \(\sqrt b s\) bounded in terms of \(C\). These are geometric inputs about the constructed family. [Matched expanders and primitive traversal](../ReflectedScattering/InfinitelyManyZeroTurnExpanders.md) · [Fixed-time averaging estimate](../ReflectedExpanders/LargeMarkerNecessaryBounds.md)

## Axis crossings near the centre

Set \(t=\sqrt b\,s,\ \epsilon=b^{-2},\ Y=\sqrt b\,X,\ K=k/\sqrt b,\ V=k_s/b\). A prime now denotes the derivative in \(t\). The exact initial-value problem is
\[
 Y'=T,\quad T'=KN,\quad K'=V,\quad V'=-K^3/2-\epsilon\,Y\cdot N,
 \qquad (Y,T,K,V)(0)=(0,e_x,0,1).
\]
On each fixed compact time interval, the solution exists for small \(|\epsilon|\) and is real analytic in \(t,\epsilon\) by analytic ODE dependence. Let \(U''=-U^3/2,\ U(0)=0,\ U'(0)=1\), and put \(w=U'\), \(u=U^2/2\), \(A(t)=\int_0^t u(r)\,dr\). At \(\epsilon=0\) the solution is
\[
 Y=(U,A),\qquad T=(w,u),\qquad N=(-u,w),\qquad K=U,\quad V=w .
\]
The first integral \(w^2+u^2=1\) gives a periodic oscillator of least period \(P\). It satisfies \(U(t+P/2)=-U(t)\). Its positive zeros are \(t_j=jP/2\), \(j=1,2,\ldots\), with \(w(t_j)=(-1)^j\). The function \(A\) is strictly increasing and \(A(t_j)=j A(P/2)>0\).

Write \(\beta=(e_b\cdot e_x)/(e_b\cdot e_y)\). A first-quarter point is on the seam line when \(Y_x-\beta Y_y=0\), where subscripts denote Cartesian components. For each fixed \(j\), the implicit function theorem gives a unique local analytic root \(t=t_j(\beta,\epsilon)\) near \(t_j\) with \(t_j(0,0)=t_j\), since the time derivative at the base point is \((-1)^j\). The rescaled position there tends to \(A(t_j)e_y\). A fixed finite list of these points therefore lies on the positive ray, at distinct positions.

Each selected point has exactly two labels. Indeed, for any sequence of further first-quarter preimages of that same point, the fast times are bounded by the preceding geometric estimate. Each subsequential limit \(t\) must satisfy \(A(t)=A(t_j)\), hence \(t=t_j\). The local uniqueness of the axis root excludes a second preimage there. The second quarter supplies the distinct label \(2s_*-t_j(\beta,\epsilon)/\sqrt b\) by reflection. An extra preimage in the centrally inverted half would force a bounded-fast-time first-quarter point on the negative ray, converging after rescaling to \(-A(t_j)e_y\). This is impossible since \(A(t)\ge0\) for \(t\ge0\). The seams themselves are at distance of order \(\sqrt b\), and the centre is distinct from the selected points.

## A first-order difference between the odd and even crossings

The reflected branches at a selected point are transverse provided the first tangent has both an axial and a transverse component. Its transverse component stays nonzero, since \(T\to(-1)^j e_x\). Vanishing of the axial component is equivalent to
\[
 G_j(\beta,\epsilon)=\beta+\frac{T_y}{T_x}\big(t_j(\beta,\epsilon),\epsilon\big)=0 .
\]
We determine the unique nearby value of \(\beta\) at which this condition holds.

The fast stress \(W=(K^2/2)T+VN\) satisfies \(W'=-\epsilon(Y\cdot N)N\), so \(W\equiv e_y\) at \(\epsilon=0\). At fixed \(t_j\),
\[
 \partial_\epsilon W_x(t_j,0)
 =\int_0^{t_j}(-Uu+Aw)u\,dt
 =-\tfrac13\int_0^{t_j}U^5\,dt .
\]
For the second equality use \(wu=(U^3)'/6\), \(A'=u\), and \(U(0)=U(t_j)=0\). The integral over a full oscillator period vanishes by antisymmetry. Over the first half-period it equals \(2\pi\), since
\[
 \int_0^{P/2} U^5\,dt
 =2\int_0^{\sqrt2}\frac{x^5\,dx}{\sqrt{1-x^4/4}}
 =8\int_0^1\frac{z^2\,dz}{\sqrt{1-z^2}}=2\pi .
\]
The exact identity \(W\cdot T=K^2/2\) gives \(T_y/T_x=(K^2/(2T_x)-W_x)/W_y\). At the base crossing \(K=0,\ W_x=0,\ W_y=1\). The shift of the crossing time makes no first-order contribution since \(W_x(t,0)=0\) identically and the differential of \(K^2\) is zero there. Consequently \(\partial_\beta G_j(0,0)=1\), and \(\partial_\epsilon G_j(0,0)\) is \(2\pi/3\) for odd \(j\) and zero for even \(j\).

By the implicit function theorem the only nearby slope giving tangency is
\[
 \beta_j(\epsilon)=
 \begin{cases}
 -\tfrac{2\pi}{3}\epsilon+O_j(\epsilon^2),&j\ \text{odd},\\
 O_j(\epsilon^2),&j\ \text{even}.
 \end{cases}
\]
Take \(j=1,\ldots,2n\). For sufficiently small positive \(\epsilon\), none of the odd tangency slopes can equal any of the even ones. The actual seam slope \(\beta\to0\) can therefore produce tangencies in at most one parity class. All \(n\) points of the other class are ordinary transverse double points. Central inversion gives \(n\) more at distinct negative heights.

For each fixed \(j\), the first label and radial position of the selected point obey \(\sqrt b\,s_j\to jP/2\) and \(\sqrt b\,|X(s_j)|\to jA(P/2)\). The argument takes a finite list of indices before sending \(b\) to infinity. A growth rate for the number of transverse double points as a function of \(b\) would require control on a growing list of crossings.

## Topology of the images

The two crossing theorems imply that these plane images realize infinitely many homeomorphism types, all at turning number zero. A primitive traversal has finitely many self-intersection label pairs by the [upper bound](CrossingComplexity.md). Away from their finitely many image points the image is locally an open arc. Each ordinary transverse double point has four local branches, so its valence as a topological point of the image is four. The number of branch points is a finite homeomorphism invariant for each image and is unbounded across the constructed family. This distinguishes the images as topological spaces. A smooth-isotopy classification would require additional arguments.

## Formal verification

The public Lean theorem `ClosedSimilarity.CrossingFrame.unbounded_primitive_ordinary_crossings` takes any natural number of requested points and any real lower bound on the centre curvature derivative. It constructs a smooth normalized homothetic expander of zero total curvature whose centre derivative exceeds that bound. Its specified arclength period is the least positive period of its Cartesian position. The selected points are distinct. In that period exactly two parameters attain each point, and the determinant of the two velocity vectors is nonzero. The opening mathematical theorem also counts points separately on the two rays and describes all sufficiently large matched markers. The formal existence statement above quantifies over the requested number of points and marker lower bound. [Main theorem](../../SolitonClassification/PrimitiveOrdinaryCrossings.lean) · [Definition of an ordinary transverse point](../../SolitonClassification/OrdinaryPointGeometry.lean)

The proof uses the same physical shooting parameters for closure, the ray at the reflection seam, and the count of intersections. Every visit to a fixed disk in fast coordinates has bounded fast time. On that bounded interval the frozen height is strictly increasing, and two adjacent candidate crossings cannot both be tangent. Signed reflection then accounts for every parameter in a full traversal. [Physical shooting sequence](../../SolitonClassification/MatchedCrossingSequence.lean) · [Seam direction](../../SolitonClassification/MatchedRayLimit.lean) · [Disk visits](../../SolitonClassification/FullQuarterCapture.lean) · [Selected quarter crossings](../../SolitonClassification/MatchedAxisVisits.lean) · [Full-period labels](../../SolitonClassification/QuarterReflectionLabels.lean)

The separate length-dependent global upper bound for arbitrary closed similarity expanders and the deduction about homeomorphism types are given in the mathematical notes. The local project audit records each new module, its source and direct-import hashes, the compiler binary and the standard-axiom check. [Global upper bound](CrossingComplexity.md) · [Verification record](OrdinaryCrossingVerification.json)
