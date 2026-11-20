# Exact covering multiplicity is constant along a smooth closed free elastic flow

Let \(X(t,\cdot)\) be a smooth regular closed plane immersion solving the free elastic flow with normal velocity \(-F N\), where \(F=k_{ss}+k^3/2\). At each time parametrize the curve by fractional arclength \(x\in\mathbb T=\mathbb R/\mathbb Z\), so \(|X_x|=L(t)\). Write \(K=Lk\). Define the curvature and position period groups by
\[
G_K(t)=\{h\in\mathbb T:K(t,x+h)=K(t,x)\ \text{for all }x\},\qquad
G_X(t)=\{h\in\mathbb T:X(t,x+h)=X(t,x)\ \text{for all }x\}.
\]
Changing the arclength origin leaves both groups unchanged.

**Theorem.** Both groups are constant in time. In particular the largest integer \(d\) for which the immersion traverses a closed regular curve \(d\) times has the same value at every time, in either temporal direction. This includes \(t=0\) for smooth regular initial data and a classical solution smooth up to the initial time. The result concerns exact global repetition of a parametrized curve. Multiplicity at a spatial intersection and closeness to a multiple covering can vary.

## A shift-equivariant curvature equation

Fix a compact interval of smooth existence and use \(d\tau=L^{-4}dt\). Since \(L>0\), passage between the two times is smooth there. Take \(T=X_x/L,\ N=JT,\ f=K_{xx}+K^3/2\), and set
\[
v=\int_{\mathbb T} K f\,dx=L^3 L',\qquad
X_\tau=L(-fN+wT).
\]
Here \(L'\) denotes physical-time derivative. Differentiating the metric \(|X_x|=L\) gives \(L_\tau=Lv\) and \(w_x=v-Kf\). We choose the unique periodic primitive with mean zero. This choice is realizable by the arclength origin. Starting from any smooth fractional-arclength chart, replacement of \(x\) by \(x+\theta(\tau)\) changes \(w\) to \(w(x+\theta)+\theta'\), so take \(\theta'=-\int_{\mathbb T}w\,dx\). This also shows that shifting \(x\) by a fixed \(h\) shifts \(w\) by the same \(h\), with no boundary term even if the curve is multiply covered.

The tangent-angle velocity is \(-f_x+Kw\), hence
\[
K_\tau=-f_{xx}+(Kw)_x.
\]
The angle lift can gain \(2\pi m\) over one period. Its derivative \(K\), its time derivative and \(w\) are spatially periodic. Expanding the curvature equation gives
\[
K_\tau+K_{xxxx}
=-\tfrac52K^2K_{xx}-3K(K_x)^2-\tfrac12 K^5+vK+wK_x. \tag{1}
\]
These formulas follow from the physical flow on one material circle, with all \(d\) traversals included in its length. [Fractional-arclength identities in the LengthGrowth project](../CurvatureMomentGap/CriticalMomentRigidity.md) · [Miura and Wheeler, free elastic flow of closed plane curves](https://arxiv.org/abs/2404.12619)

## A shift difference can never acquire or lose an exact zero

Fix arbitrary \(h\in\mathbb T\), abbreviate \(K_h(x)=K(x+h)\) and put \(z=K_h-K\). All \(L^2\) norms in this argument are on the fixed unit parameter circle. The scalar \(v\) is exactly the same for the two translates. The two zero-mean tangential velocities satisfy
\[
\partial_x(w_h-w)=-\left(K_h(K_h)_{xx}-KK_{xx}+(K_h^4-K^4)/2\right).
\]
Uniform smooth bounds on the chosen compact time interval and periodic Poincaré therefore give
\[
\|w_h-w\|_2\le C(\|z\|_2+\|z_{xx}\|_2).
\]
Indeed the difference of the second-order products is \(K_hz_{xx}+zK_{xx}\). When subtracting \(wK_x\) in (1), use \(w_hz_x+(w_h-w)K_x\). The remaining polynomial terms involve at most two derivatives of \(z\) with bounded coefficients. Integration by parts bounds \(\|z_x\|_2^2\le\|z\|_2\|z_{xx}\|_2\). Thus, with the positive self-adjoint periodic operator \(A=1+\partial_x^4\) and \(g=z_\tau+Az\),
\[
\|g\|_2\le C\langle Az,z\rangle^{1/2},\qquad
\langle Az,z\rangle=\|z\|_2^2+\|z_{xx}\|_2^2 . \tag{2}
\]
The constant can depend on the solution and the time interval and is independent of the shift \(h\).

For forward uniqueness let \(Z=\|z\|_2^2\). From (2),
\[
Z'=-2\langle Az,z\rangle+2\langle g,z\rangle\le(C^2/2)Z .
\]
Thus \(Z=0\) at one time implies \(Z=0\) at every subsequent time in the interval.

For backward uniqueness, while \(Z>0\) put \(Q=\langle Az,z\rangle/Z\). By periodic integration by parts and the quotient rule,
\[
 Q'=-2\|(A-Q)z\|_2^2/Z+2\langle(A-Q)z,g\rangle/Z
 \le \|g\|_2^2/(2Z)\le C^2Q/2 .
\]
Also \((\log Z)'\ge-2Q-2C\sqrt Q\). Starting with \(Z(s)>0\), the bound \(Q(u)\le e^{C^2(u-s)/2}Q(s)\) prevents \(\log Z\) from decreasing to minus infinity at any finite later time. This excludes a first subsequent zero. Together the two implications prove that membership of every fixed \(h\) in \(G_K\) is independent of time. All estimates use finite smooth intervals. For initial data smooth up to \(t=0\), they hold on the closed initial slab with a one-sided derivative there. In particular the proof requires no analyticity of the initial parametrization.

## Recovering the multiplicity of the actual immersion

The turning number \(m=(2\pi)^{-1}\int_{\mathbb T}K\,dx\) is an integer and is constant by regular homotopy, equivalently by integrating the divergence form of the curvature equation. If \(K\) is nonconstant, \(G_K\) is a proper closed subgroup of \(\mathbb T\), hence it is \(\{j/N\bmod1:0\le j<N\}\) for some integer \(N\ge1\). Indeed an infinite subgroup has nonzero elements arbitrarily close to zero and is dense. This \(N\) is fixed by the preceding argument.

Any period of \(X\) is a period of its tangent and signed curvature. For \(h=j/N\) the angle advance \(\int_x^{x+h}K\,dy\) is constant in \(x\), with value \(2\pi mj/N\) for the representative \(0\le j<N\). Thus \(T(x+h)=T(x)\) exactly when \(N\) divides \(mj\). In this case \(X(x+h)-X(x)\) is a constant vector, since its derivative vanishes. Adding \(N\) copies of this difference gives zero by periodicity of \(X\), so the vector itself is zero. Therefore
\[
                 G_X=\{j/N\bmod1:N\mid mj\},\qquad
                 |G_X|=\gcd(N,|m|).
\]
In particular \(m=0\) gives all \(N\) position periods; a repeated support block with nonintegral turning does not by itself return the position and tangent.

If \(K\) is spatially constant on one slice, \(G_K=\mathbb T\) on the entire time interval, so every slice has constant curvature. Closure excludes zero curvature. Each slice has \(K=2\pi m\), is a round circle traversed \(|m|\) times, and \(G_X=\{j/|m|\bmod1\}\).

Finally, any orientation-preserving reparametrization \(\phi\) satisfying \(X\circ\phi=X\) has \(\phi'=1\) in fractional arclength, by equality of the two speeds. It is a translation. Conversely a period of size \(1/d\) makes the immersion factor through the \(d\)-sheeted circle covering. Thus the group computation measures the exact geometric covering number, including the primitive case \(d=1\).

The finite-time lower bound depends on the solution and the interval. Increasingly accurate approximate repetitions along an unbounded trajectory and the universal fourth-root upper bound for length remain open.

The Lean module `LengthGrowth.ActualFlow.FrequencyBackward` verifies the scalar inference used in the backward direction. Its theorems `LengthGrowth.FrequencyBackward.first_zero_lower_bound` and `LengthGrowth.FrequencyBackward.positive_at_right` take the two differential inequalities for \(Q\) and \(Z\) as hypotheses. They give an explicit lower bound at a putative first zero and propagate positivity throughout any finite interval. Here the constants are \(a=C^2/2\), \(b=2\) and \(c=2C\) in the inequalities \(Q'\le aQ\) and \(Z'\ge -(bQ+c\sqrt{Q})Z\). The derivation from the curvature equation, the norm estimates, forward uniqueness and the computation of the immersion's covering number are the written arguments above.
