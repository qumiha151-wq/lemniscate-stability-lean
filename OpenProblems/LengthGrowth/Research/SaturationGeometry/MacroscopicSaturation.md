# Saturation on the root-mean-square curvature time scale

Let \(F=k_{ss}+k^3/2,\ E=\frac12\int k^2ds,\ D=\int F^2ds,\ U=EL\). Set \(\lambda=E/(2L)>0,\ \eta=LU'/E^3\). The physical identities \(E'=-D,\ L'=\int kF\,ds\) give
\[
 \rho:=\tfrac12-\eta=\frac{L^2}{E^3}\int (F-\lambda k)^2\,ds .       \tag{1}
\]
RMS units mean that space is first dilated by the initial root-mean-square curvature \((2E(0)/L(0))^{1/2}\), and time by its fourth power. Thus \(\lambda(0)=1/4\). On these units the [fast time scale of spatial stress profiles](DynamicSaturation.md) becomes a vanishing interval as \(U(0)\to\infty\). Indeed \((\epsilon E_0)^4/(2E_0/L_0)^2=U(0)^{2/3}/4\).

## Exact compatibility in a spacetime limit

Consider a smooth material patch of a free elastic flow on a nonempty open time interval. If \(F=\lambda(t)k,\ \lambda(t)>0\), with \(\lambda\) continuously differentiable, every spatially connected patch is flat or has constant curvature in space at each time. In fact on each time slice the exact spatial first integral is
\[
 k_s^2=C(t)+\lambda k^2-k^4/4 .
\]
The material curvature equation \(k_t=-F_{ss}-k^2F\) gives \(k_t=-\lambda^2k-\lambda k^3/2\). Using the material commutator \([\partial_t,\partial_s]=-kF\partial_s\) to differentiate the force gives
\[
 F_t=-F_{ssss}-\tfrac52 k^2F_{ss}-5kk_sF_s
       -(3k_s^2+4kk_{ss}+\tfrac32 k^4)F .
\]
Substitution of \(F=\lambda k,\ k_{ss}=\lambda k-k^3/2\) and its second spatial derivative yields on \(k\ne0\)
\[
 \lambda'=-\lambda(5k_s^2+4\lambda k^2-k^4)
          =-\lambda\big(5C(t)+9\lambda k^2-\tfrac94 k^4\big).       \tag{2}
\]
This is a nonconstant polynomial in \(k^2\) with fixed value. The curvature is constant on each connected component where it is nonzero, and continuity excludes a finite boundary with zero curvature inside the patch. At a point with nonzero curvature, a neighborhood in spacetime has \(k^2=2\lambda\). The curvature equation forces \(\lambda'=-4\lambda^3\) there. Thus any smooth patch with \(F=\lambda k\) and the *global saturation law* \(\lambda'=-6\lambda^3\) is flat.

## A proved exclusion under a uniform bound on curvature derivatives

Fix \(T>0\) and \(B<\infty\). A sequence of genuine closed flows with \(U_j(0)\to\infty\), in initial RMS units on \(0\le t\le T\), cannot satisfy both
\[
 \sup_{j,t,s}\max_{0\le m\le10}|\partial_s^m k_j(t,s)|\le B,\qquad
 \sup_{0\le t\le T}\rho_j(t)\longrightarrow0.                       \tag{3}
\]
The derivative bounds here are hypotheses. The result excludes sustained saturation in this regular regime at one fixed macroscopic duration.

To prove it, write \(R=F-\lambda k\). From (1),
\(\|R\|_2/\sqrt L=(2\lambda)^{3/2}\sqrt\rho\). Cauchy–Schwarz gives
\[
 L'/L=4\lambda^2+O(\lambda^2\sqrt\rho),\qquad
 D/E=2\lambda^2+O(\lambda^2(\sqrt\rho+\rho)).
\]
Consequently \((\lambda^{-2})'=12+O(\sqrt\rho+\rho)\) and the \(\lambda_j\) converge uniformly on the entire interval to \(\lambda(t)=(16+12t)^{-1/2}\). The length ratios \(L_j(t)/L_j(0)\) stay bounded above and below. The initial RMS lengths tend to infinity since \(L_j(0)^2=2U_j(0)\).

Use material origins with initial arclength coordinate \(x\). The density \(g=ds/dx\) starts at one and \(g_t=kF g\), so (3) bounds \(g^{\pm1}\) uniformly. The spatial proportion at time zero with \(|k_j|\ge1/2\) is bounded below by a positive constant, by the curvature bound and initial mean square one. Average over all initial origins \(x_0\) the spacetime residual on \([0,T]\times[x_0-2,x_0+2]\) using \(dt\,dx\). Periodicity, the density and length comparisons, and (1) show that its mean tends to zero. Hence for each \(j\) one may choose an origin with \(|k_j(0,x_0)|\ge1/2\) and local squared residual tending to zero.

On this fixed-label window let \(k_m=\partial_s^m k\). For each \(m\le6\), its material time derivative is uniformly bounded by (3): commute through the \(m\) arclength derivatives in the curvature equation; each resulting term is a finite sum of products of jets up to order \(m+4\). The spatial derivative in \(x\) is \(gk_{m+1}\) and is also bounded. The densities \(g\) are equicontinuous in \(x,t\), by differentiating \(g=\exp\int_0^t kF\,dr\) in \(x\) and using the preceding first spatial derivative estimates. Extract locally uniform limits of \(g\) and the jets through order six. They satisfy \(\partial_s=g^{-1}\partial_x\) and the curvature and force evolution equations: integrate their exact material derivative formulas (for \(k\) and \(F\)) in time, using the uniformly convergent jets. The residual vanishes in the limit, giving \(F=\lambda k\). The origin has nonzero initial curvature and therefore also nonzero curvature in a nearby open spacetime patch. Equation (2) contradicts \(\lambda'=-6\lambda^3\). This proves (3).

Thus a putative single flow approaching the maximal rate on such consecutive intervals must leave every uniform bound of this kind. Obtaining smooth nonflat limits or handling concentration of the curvature and its derivatives from the unrestricted hypotheses remains open.

## Rising records at any fixed strict rate

For every \(a<1/2\) there are constants \(T_a,\delta_a>0\) and smooth **primitive turning-zero** closed flows with arbitrarily large \(U(0)\) such that, in initial RMS units, \(\eta(t)>a\) throughout \([0,T_a]\) and \(U(T_a)>(1+\delta_a)U(0)\).

First modify the [saturating packet](DynamicSaturation.md) to obtain a single smooth closed turning-zero curve with \(\eta(0)>\max(a,0)\). Start a flat-ended, zero-total-turn packet along \(e_x\). Follow it by its reflection across the horizontal axis, with the same initial tangent \(e_x\). The combined displacement is horizontal. Attach three smooth fixed flat-ended turning bumps with respective integrals \(\pi/2,-\pi,3\pi/2\). At the intermediate vertical up and vertical down tangencies insert straight segments of suitable nonnegative lengths so that the net vertical displacement of these three bends and segments is zero. These lengths are bounded independently of packet size because the oscillatory pair has zero vertical displacement. The final tangent is \(-e_x\). Insert a horizontal straight segment whose length makes the total half-block length equal to its integrated \(k^2\); the excess energy of the long periodic packet makes this length positive. The half-block has horizontal displacement and turn \(\pi\). For the second half reflect its tangent field across the vertical axis. It starts with \(-e_x\), ends with \(e_x\), cancels the displacement of the first half and turns through \(-\pi\). The resulting closed unit-speed immersion has turning zero and RMS curvature one. Only fixed-length pieces contribute to \(\int(F-k/4)^2\) outside the exact oscillator cores and straight segments, so (1) again gives \(\eta(0)\to1/2\) as the packet grows.

Choose one such curve. Smoothness and continuity of the genuine flow yield \(T>0\) on which \(\eta>\max(a,0)\) with positive margin and \(U(T)/U(0)>1\). An \(n\)-fold traversal evolves exactly as the same \(n\)-fold traversal of this flow. It multiplies \(L,E,D,L'\) by \(n\), so it multiplies \(U\) by \(n^2\) and preserves both \(\eta\) and RMS units.

For each fixed \(n\) perturb its initial immersion arbitrarily slightly in the smooth topology so it is primitive. Place the long horizontal straight segment between the first packet and its mirrored copy, each curved arbitrarily close to that joint. The two resulting long straight segments of the base curve are strictly longer than any other straight interval once the packet is fixed sufficiently large. Shorten the maximal flat length in every repeated copy of these long segments except one by a small smooth normal graph supported at its midpoint, nonzero at that midpoint, with arbitrarily small height. Choose a bump whose support lies strictly inside the segment, with analytic non-affine interior, so the replacement leaves two strictly shorter straight subsegments. The curve then has a unique maximal straight interval. A nontrivial arclength covering period would have to preserve this single proper interval on the parameter circle, which is impossible for a nonidentity circle translation. Turning number remains zero under the sufficiently small perturbations.

Smooth continuous dependence of the elastic flow on its smooth immersed initial data, modulo reparametrization, preserves the strict \(\eta\) inequality and relative \(U\) gain on a slightly shorter common interval, for perturbations chosen separately at each fixed \(n\). Equivalently one may first choose the base inequalities on \([0,2T_a]\) and a strict gain by \(T_a\), leaving room for the small change of the perturbed initial RMS factor. In a parametrized strongly parabolic gauge the leading term is \(-|\gamma_u|^{-4}\partial_u^4\gamma\); the lower terms depend smoothly on derivatives through order three on the open immersion condition. Standard local quasilinear continuous dependence in high regularity on the parameter circle therefore applies for each fixed \(n\), by continuation along the smooth reference solution. No uniform size of the perturbation neighborhood is needed. The resulting actual trajectories prove the assertion with a single \(T_a,\delta_a\), while \(U(0)\to\infty\). The exact covering rigidity already established for positive times also preserves primitivity along each perturbed flow if one needs a later-time assertion. [Elastic curve evolution](https://epubs.siam.org/doi/10.1137/S0036141001383709) · [Quasilinear continuous dependence](https://www.math.uzh.ch/amann/files/qppvmaxreg.pdf)

The earlier project note *LengthNormalizedClock*, §5, had already shown by a different elliptic-wave construction that initial values can approach \(\eta=1/2\) in every fixed turning class. Here the positive-time gain and the time-dependent incompatibility give further conclusions.

## Cost on the running record of one trajectory

There is also an exact budget on the set of record heights gained at a prescribed positive rate. Let \(d=DL^2/E^3\). At times when \(U'>0\), Cauchy–Schwarz gives \(\eta+d=LL'/E^2\le\sqrt{2d}\). Thus, for \(0<a\le1/2\), on \(\eta\ge a\),
\[
 \frac{D/E}{U'/U}=\frac d\eta
 \ \ge\ \frac{1-\sqrt{1-2\eta}}{1+\sqrt{1-2\eta}}
 \ \ge\ c_a:=\frac{1-\sqrt{1-2a}}{1+\sqrt{1-2a}}.
\]
For \(U(0)<h\le\max_{[0,T]}U\), let \(t_h\) be the first hitting time. Let \(H(t)=\max_{[0,t]}U\). This running maximum of a \(C^1\) function is locally Lipschitz, with \(H'=0\) off the contact set and \(H'=U'\) almost everywhere where \(H'>0\). The time integral against \(H'/H\) pushes forward by \(H\) to \(dh/h\); intervals where \(H\) is constant contribute zero. The first hit is its inverse except for the at most countable plateau values. It follows that
\[
 c_a\int_{U(0)}^{H(T)} {\bf1}_{\{\eta(t_h)\ge a\}}\,\frac{dh}{h}
 \ \le\ \log\frac{E(0)}{E(T)} .
\]
On a hypothetical unbounded trajectory with \(E_\infty>0\), every set of record heights gained above a fixed positive rate therefore has finite logarithmic measure. If \(E_\infty=0\), this budget can diverge. The positive-time examples above allow a fixed positive relative gain for every fixed threshold strictly below \(1/2\). They do not stitch together infinitely many successively growing records on any one curve. Uniform limits, constraints on an exact flow, the record budget, and the construction in this note are written proofs, without Lean verification.

The actual-flow energy and dissipation identities are checked separately. The local limiting compatibility, perturbation to a primitive flow and logarithmic record budget are written results. A subsequent compactness argument removes the derivative hypothesis for the exclusion of a bounded integrated deficit on a fixed RMS window. [Physical energy dissipation](../../LengthGrowth/ActualFlow/ForwardDissipation.lean) · [Integrated deficit theorem](MacroscopicDeficitBudget.md)
