# An exact match on a short arc determines a return

Let \(X(t)\) be a smooth regular closed planar free elastic flow, smooth up to its initial immersion at \(t=0\). Suppose that two open arcs of the flow at **different positive times** coincide up to a direct plane similarity and a smooth change of parameter. The arcs may be arbitrarily short. Then the two complete parametrized slices agree up to that similarity and a diffeomorphism of the parameter circle. In particular the two-sided fourth-root length bound and the return classification apply. A flow violating the fourth-root upper bound cannot have such a pair of matching arcs.

## Spatial analyticity

Here is a proof for closed curves starting from the actual flow equation. Use fractional arclength \(x\) on the unit circle, normalized curvature \(K=Lk\) and time \(d\tau=L^{-4}dt\). With the zero-mean tangential gauge the equation in the [return theorem](SimilarityReturns.md) has the form

\[
 K_\tau + K_{xxxx} =
 -\tfrac52 K^2 K_{xx} -3K(K_x)^2-\tfrac12 K^5+vK+wK_x,\qquad
 v=\int_0^1 (KK_{xx}+K^4/2)\,dx,\quad w_x=v-KK_{xx}-K^4/2,\quad \int_0^1 w=0 .
\]

For \(j=0,2\) use the Fourier norm
\[
\|u\|_{j,r}=\sum_{n\in\mathbb Z}(1+|n|)^j e^{r|n|}|\widehat u(n)|.
\]
These weighted summable-sequence spaces are Banach algebras. Derivatives up to order two map the \(j=2\) space boundedly to the \(j=0\) space. Taking the mean or the zero-mean primitive is bounded at order zero. Consequently the entire right-hand side is bounded and Lipschitz on each order-two ball, with values at order zero. All constants are uniform in \(r\ge0\).

Start at normalized time \(\sigma\) and take \(r(\tau)=\tau-\sigma\). For \(0<h\le1\), the semigroup multiplier \(e^{-h(2\pi n)^4}\) maps the radius \(r\) to \(r+h\) with order-zero to order-two operator norm at most \(C(1+h^{-1/2})\). Indeed its weighted multiplier is bounded by \((1+|n|)^2\exp(h|n|-h(2\pi n)^4)\). The order-two to order-two norm is bounded by a constant. In the space with norm \(\sup_{0\le h\le\epsilon}\|u(\sigma+h)\|_{2,h}\), Duhamel's integral map on the ball of radius \(2C(\|K(\sigma)\|_{2,0}+1)\) maps into that ball and is a contraction for small \(\epsilon\), since \(\int_0^\epsilon(1+h^{-1/2})\,dh\to0\). One can use continuous weighted Fourier coefficient vectors in \(\ell^1\), including at \(h=0\); strong continuity of the linear semigroup follows by dominated convergence. The same contraction estimate in the unweighted norm gives uniqueness among bounded solutions there by subdivision. The smooth physical solution satisfies the Fourier integral equation and thus agrees with this solution. On compact smooth time intervals the unweighted order-two norm is uniformly bounded, for example by four spatial derivatives and the summability of \((1+|n|)^{-2}\). This makes the admissible \(\epsilon\) uniform and reaches each positive time from an earlier slice.

It follows that \(K\) at every positive time is real analytic in fractional and physical arclength. The Frenet equations reconstruct the tangent and position as real analytic functions on the entire real arclength line. This analyticity conclusion concerns geometric arclength and needs no analytic initial parametrization.

## Recovering the full number of traversals

Choose unit-speed lifts \(\gamma_i:\mathbb R\to\mathbb R^2\) at the two times. If their arcs match by \(S(z)=d+\lambda Rz\), \(\lambda>0\), differentiating the arclength norms makes the change of arclength parameter affine. Thus locally
\[
 \gamma_2(c+\varepsilon\lambda s)=S\gamma_1(s),\qquad \varepsilon\in\{-1,1\}.
\]
The identity theorem extends this equality to every real \(s\). It also suffices to know this same equality on an infinite set of arclength labels with a finite accumulation point. The real period group of a nonconstant closed curve has a least positive generator; the identity just proved shows that these two primitive lengths have ratio \(\lambda\). The total length of each slice equals its primitive length times the number of exact traversals. This latter integer is invariant along the smooth physical flow, including for turning number zero. Hence the total lengths have ratio \(\lambda\) and the affine arclength correspondence descends to a diffeomorphism of the full parameter circles. This proves the assertion. [Proof of exact covering invariance](../../../LengthGrowth/Research/ExactRecurrence/CoveringRigidity.md)

## Detecting a continuous expander from one slice

At any single positive time, suppose the curvature and position obey the similarity equation
\[
 k_{ss}+k^3/2=-a(X-O)\cdot N-b(J(X-O))\cdot N
\]
at all arclengths in a nonempty open arc, or just on a set with a finite accumulation point in arclength. Here \(a,b\) and \(O\) are fixed on the tested set. Analyticity makes the equation hold on the entire slice. Translation and rotation balance for the elastic force and the dilation virial give \(\int F^2 ds=aE\), hence \(a>0\). Starting at this slice and rescaling by \(\rho=(1+4a\,\Delta t)^{1/4}\), rotating through \((b/a)\log\rho\) about \(O\), gives a genuine geometric free elastic flow by the normal velocity equation. Two-sided uniqueness identifies it with the given flow on their common time domain. The model's backward zero of \(\rho\) cannot lie at or after the original initial time: the model energy would diverge there while the given flow is smooth. The continuous self-similarity therefore holds throughout the given flow.

These are written proofs. The local analytic continuation, the traversal argument and the passage to an actual geometric flow have not been formalized in Lean in this module.
