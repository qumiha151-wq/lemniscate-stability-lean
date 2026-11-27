# Detecting an exterior similarity centre from the elastic force

Let \(X\) be a smooth closed arclength-parametrized free-elastic similarity profile, with its fixed similarity centre at zero. Put \(T=X'\), \(N=JT\), \(T'=kN\), \(p=X\cdot N\), \(q=X\cdot T\), and
\[
 F=k''+k^3/2=-ap-\omega q,\qquad a>0.
\]
The curve may self-intersect and may traverse its image several times. Its tangent turning number \(m\) refers to the chosen period. If the centre is exterior to the convex hull, the homothetic or rotating expanding motion gives a strict half-plane migration from any chosen time to sufficiently large later times. If the centre belongs to the hull, all forward similarity hulls share it. [Proof of the two-time equivalence](../SimilarityMigration.md)

## Two exclusions for the entire similarity motion

1. If the number \(Z\) of true sign changes of \(F\) on one period satisfies \(Z<2|m|\), the centre is in the hull at every time. If the profile avoids the centre, its initial hull contains the disk of radius \(\min|X|\) about zero.
2. A single arc on which \(F\) has constant weak sign and \(\left|\int k\,ds\right|\ge2\pi\) prevents migration, at any global turning number, including zero. More generally, suppose for each unit vector \(n\) there is either a label with \(N=n,\ F\ge f\), or a label with \(N=-n,\ F\le-f\). Here \(f\ge0\). Then
\[
 \overline B\bigl(0,f/\sqrt{a^2+\omega^2}\bigr)\subset \operatorname{conv} X .
\]
The labels can lie on different arcs. The common future disk can use this initial radius because the dilation factor is at least one.

For the second test, \(F=-X\cdot(aN+\omega T)\); \(aN+\omega T\) is a fixed rotation and dilation of \(N\). The witnesses therefore furnish a point below height \(-f/\sqrt{a^2+\omega^2}\) in every direction. Separation from a point in the claimed disk is impossible. A continuous lifted tangent angle changes by \(\int k\,ds\). A change of at least one complete turn realizes every normal direction by the intermediate value theorem, even on a nonmonotone arc.

For a direct proof of the first test, suppose the signed normal cover at \(f=0\) fails. Some unit \(n\) has \(F<0\) at every label of normal \(n\) and \(F>0\) at every label of normal \(-n\). Start at a point of normal \(n\). Over one period the lifted normal angle changes by \(2\pi m\). Taking successive first hits of its levels at increments \(\operatorname{sign}(m)\pi\) gives \(2|m|+1\) strictly ordered labels at alternating normals. The actual forces at consecutive labels have strict opposite signs. Hence \(Z\ge2|m|\). In the case \(m=0\), the second test or the exact index below can still apply.

## Exact winding from intrinsic force zeros

Use the previously established intrinsic companion \(h=aq-\omega p\). Differentiating \(p'=-kq,\ q'=1+kp\) gives \(F'=kh-\omega\) and \(h'=a-kF\). In particular \(h=(F'+\omega)/k\) off curvature zeros. For a nonround closed profile the curvature and position are real analytic by the profile ODE, and curvature has both signs by half-RMS rigidity. At a curvature zero of order \(j\), \(h\) extends by analytic division, with value \(F^{(j+1)}/k^{(j)}\). If \(\omega\ne0\), \(k'''=-\omega\) at any curvature zero, so \(j\le3\). If \(\omega=0\) and \(k=k'=k''=0\), then \(p=0\) and uniqueness gives the straight radial solution, which cannot close. Thus \(j\le2\) for a closed pure expander. The constants are also recoverable: \(a=L^{-1}\int kF\,ds\), and for nonround profiles \(\omega=-F'\) at any curvature zero. Circular profiles have their usual redundant rotation parameter. [Intrinsic identities and inflection jets](../../../SolitonClassification/IntrinsicRotationAndOddExclusion.txt) · [Curvature-sign rigidity](../../../SolitonClassification/CurvatureSignRigidity.txt)

Let \(\theta\) be a lift of the tangent angle. In complex notation,
\[
 h+iF=(a-i\omega)e^{i\theta}\overline X . \tag{1}
\]
If some zero of \(F\) also has \(h=0\), the profile actually passes through its centre. Otherwise the curve avoids zero. Assign each sign-changing zero of \(F\) the sign \(\epsilon=+1\) for negative-to-positive and \(-1\) for positive-to-negative. Then its position winding \(w\) about the centre is exactly
\[
 w=m-\sum_{\{F=0,\ h>0,\ F\ {\rm changes\ sign}\}}\epsilon . \tag{2}
\]
To prove this, lift the argument of the nonzero loop \(h+iF\). Its degree is the signed number of crossings of the positive real ray. An odd-order tangency with sign change counts once in the appropriate orientation, since its local angle passes from one side of this ray to the other. An even-order contact contributes zero. The conclusion follows equivalently by decomposing the circle at the isolated zeros, using the upper or lower half-plane argument on each open interval, and keeping track of its limiting values on the same ray. The analytic function \(F\) is nonzero somewhere, since \(F\equiv0\) would contradict the dilation virial \(\int Fp=-\frac12\int k^2\). Thus the count is finite. Formula (1) gives \(\deg(h+iF)=m-w\). Because the total numbers of upward and downward force crossings are equal, \(2|m-w|\le Z\). Nonzero \(w\) forces every ray from the centre to meet the profile. Every support is then at distance at least \(\min|X|\) from the centre, proving the disk statement in the first test. The signed formula still detects centre containment when \(Z\ge2|m|\).

## A finite criterion for the zero-winding case

A loop of index zero can surround its centre with its convex hull. The following additional test decides exactly whether it does so, using finite scalar data of the curvature. Define
\[
 D=a^2+\omega^2,\quad B=ah-\omega F=Dq,\quad G=aF+\omega h=-Dp .
\]
Check centre passages first as above. If the centre is avoided, \(B+iG=D e^{i\theta}\overline X\) never vanishes. Fix a continuous polar angle \(\alpha\) along a cut period. Its derivative is \(G/(D|X|^2)\). The analytic function \(G\) cannot vanish identically: then \(X\) is tangent to each of its radii and its polar angle is constant, which is incompatible with a closed regular immersion. If \(G\) never changes sign, \(\alpha\) changes through a nonzero integer multiple of \(2\pi\) and the centre belongs to the hull.

Otherwise cut at a sign-changing zero and partition the cyclic material period at all such zeros of \(G\). On each resulting arc \(I=[l,r]\), the polar angle is monotone. Its increment is exactly
\[
 A_I=\int_l^r k\,ds-
 \frac{\pi}{2}\,\operatorname{sign}(G|_{I^\circ})
       \bigl(\operatorname{sign}B(l)-\operatorname{sign}B(r)\bigr). \tag{3}
\]
Here the sign on the interior means the weak sign off the finitely many zeros. Indeed \(\theta-\alpha\) is an argument of \(B+iG\) and stays on a single closed upper or lower semicircle over the arc. Its endpoint values therefore differ by precisely the second term. This proof includes intermediate even-order zeros of \(G\) and arbitrary orders at the two endpoints.

Form the list of partial sums of \(A_I\) starting at zero and including their total \(2\pi w\). If \(w\ne0\), the centre is inside. When \(w=0\), the maximum minus the minimum of this finite list is the exact polar-angle oscillation. The centre is exterior if and only if that number is **strictly less than** \(\pi\). A continuous loop in an open viewing half-plane has a branch of smaller oscillation by compactness. Conversely a branch of smaller oscillation lies strictly in the open half-plane centered on its midrange. Equality includes the centre in the hull. In particular any monotone polar arc or concatenation of arcs with angular span at least \(\pi\) rules out a migrating similarity flow. The test needs the intrinsic curvature, the signs at isolated roots and scalar integrals over the resulting finite arcs. Finding a new closing scalar curvature with the strict exterior inequality remains an existence problem.

## Application to the certified nonsymmetric rotating profile

For the [primitive expander with integer winding](../../../SolitonClassification/RotatingCertificate/IntegerWinding/DyadicReset/PrimitiveRotatingProfile.md), \(a=1\), \(0.10<\omega<0.11\), and \(m=-1\). Its elastic force changes sign **exactly 74 times**. All those zeros are simple. For \(h>0\) the count is 19 upward and 19 downward crossings. For \(h<0\) there are 18 upward and 18 downward crossings. Thus (2) recovers \(w=-1\) from force crossings. The [Fourier replay](force_indices.py) reads the published degree-3200 Fourier input with the source hash in [its report](force_indices.json). It applies the [existing uniform true-orbit error](../../../SolitonClassification/RotatingCertificate/IntegerWinding/Fourier/WholeOrbitFourier.md) on all 65,536 cells. On every cell where the enclosure of \(F=-(p+\omega q)\) contains zero, it checks \(F'=k(q-\omega p)-\omega\) strictly away from zero. Both endpoint signs decide existence, and the interval value of \(h=q-\omega p\) decides which ray was crossed. It checks the periodic wraparound cell as well.

An independent integer computation gives the uniform signed-normal force margin **\(f=0.642233105\)**. Consequently the initial hull contains the disk of radius **0.638** about the similarity centre. At dilation factor \(\rho\) the disk has radius \(0.638\rho\). To reproduce the [normal cover](cover.json), pass the folder containing the original signed 4000-cell tapes to [normal_cover.py](normal_cover.py). Source hashes for both complete decompressed tapes are verified. The original [node transport](../../../SolitonClassification/SolitonClassification/Rotating/IntegerGlobalNodePositions.lean) and [interior state bounds](../../../SolitonClassification/SolitonClassification/Rotating/IntegerGlobalPhysicalBounds.lean) furnish errors below \(10^{-9}\) on all six coordinates of the interior nodes and absolute bounds ten on the first five state coordinates along the arcs.

Here are the error details. The state is \((k,u,p,q,\omega,\theta)\) with \(k'=8u\). Since \(|p'|\le100,\ |q'|\le101,\ |k'|\le80\), from the nearer of the two endpoint enclosures every interior point is at distance less than \(1/250\) in arclength. The exact identity for \(F'\) now supplies a uniform bound on that whole cell and proves a strict positive or negative force margin. The endpoint enclosures of \(\theta\), by the intermediate value theorem, give an interval of actual tangent directions. Negative force witnesses have their angles shifted by \(\pi\); to both types add arbitrary integer multiples of \(2\pi\). Intersections of rational inner angle intervals prove coverage from zero through an upper bound for \(2\pi\), in 163 overlapping cells. Rotating the full tangent circle through \(\pi/2\) gives the signed normal cover. The checker uses integer arithmetic in units of \(10^{-9}\), with outward rounding; the enclosures of \(\pi\) follow from rational alternating arctangent sums and Machin's identity. The stated disk follows from \(0.638\sqrt{1+0.11^2}<0.642\).

The examples therefore furnish whole-time overlap, including a profile without any Euclidean symmetry. Other shooting boxes where only an approximate return is known cannot furnish a migration witness. A finite cyclic symmetry already puts its centre in the hull, while zero position winding alone cannot establish exteriority. The near-homothetic examples with an exterior fitted centre and small relative force residual give a different limitation: a small fitting error at a single slice does not guarantee that the actual flow follows the fitted dilation. [Numerical and validated radial shots](../FiniteRadialShooting/FiniteRadialShooting.md) · [Exterior fits](../ExteriorOptimalFit/OptimalExteriorDefect.md)

## Verification scope

The independent Migration Lean project verifies the true companion and centre-passage identities, the signed normal cover's centered disk, the full-turn force-arc implication and the alternating-sample force-count obstruction for the actual rotating spatial equation. The signed winding formula, finite polar extremum calculation and bounds for the named orbit are written proofs with the two explicit interval replays. Ordinary convex hulls and physical similarity times are connected by the earlier verified direct-similarity lemmas. Existence of a closed free elastic flow with a pair of strictly separated slices remains open.
