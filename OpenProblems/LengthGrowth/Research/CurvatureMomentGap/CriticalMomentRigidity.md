# Rigidity at the centered cubic-moment threshold

Consider smooth immersed closed planar free elastic flow with normal velocity \(-F N\), where \(F=k_{ss}+k^3/2\). Write \(L\) for length, \(E=\tfrac12\int k^2\,ds\), \(U=LE\), and \(S=\int k\,ds=2\pi n\). The following results concern smooth forward flows existing for all physical times.

On each slice normalize length to one. Denote normalized curvature, force and arclength by \(K=Lk\), \(f=L^3F\) and \(x\in\mathbb R/\mathbb Z\). All integrals below use \(dx\). Define
\[
 b=\int K^2=2U,\quad c=\int K^3,\quad d=\int f^2,\quad v=\int K f,\qquad
 G=|c|/b^{3/2},\quad J=|2c-bS|/b^{3/2}.
\]
The quantity \(b\) is bounded below by \(4\pi^2\), by periodic Wirtinger applied to the mean-zero unit tangent.

**Theorem.** Suppose \(U\) is bounded on a tail and \(\liminf J\ge1\). Then \(n\ne0\) and the length-normalized flow converges smoothly, up to reparametrization, to the round \(|n|\)-fold circle. If \(J\ge1\) eventually, the upper bound on \(U\) follows from the flow. More generally, for each \(M<\infty\) there is \(\eta(M)>0\) such that every flow with \(U\le M\) on a tail either converges to this smooth circular limit or satisfies \(\liminf J\le1-\eta(M)\). In turning number zero this yields \(\liminf G\le \tfrac12-\eta(M)/2\).

In particular, no turning-zero flow can satisfy \(G\ge\tfrac12\) eventually, even in the absence of an assumed energy-length bound. The uniform gap \(\eta(M)\) is an existence result.

**Corollary without an energy cap.** Every smooth closed flow has \(\liminf J\le1\), with equality if and only if its length-normalized curves converge smoothly, up to reparametrization, to a multiply covered round circle, including the single cover. For each fixed nonzero turning number \(n\), there is \(\delta_n>0\) such that \(\liminf J>1-\delta_n\) suffices for this convergence. The final section proves these statements using the independent static cubic-moment gap.

## Exact dissipation and finite windows

Use the clock \(d\tau=L^{-4}dt\). It reaches infinity for a trajectory with bounded \(U\) on a tail. Indeed the secant bound \(|L(t)-L(s)|^2\le(t-s)(E(s)^2-E(t)^2)\) implies \(L(t)=O((1+t)^{1/4})\): if \(L(t)>2L(0)\), restart at the last point \(s\) with \(L(s)=L(t)/2\), obtaining \(L(t)^4\le16t\sup U^2\). A continuous finite prefix has bounded \(U\). The first variations give \(-U_\tau=d-bv/2=:\delta\), and \(\int f=c/2\). An exact expansion gives
\[
 16\delta=\int(4 f-bK-(2c-bS))^2 + b^3(J^2-1).
\]
Thus \(J\ge1\) makes \(U\) nonincreasing. This applies in physical time even before the range of the normalized clock is known.

For a single bounded flow with \(\liminf J\ge1\), select late times approaching the tail lower limit of \(U\). After passing to a subsequence, the ensuing unit windows in \(\tau\) satisfy \(J\ge1-\varepsilon_j\) and \(U(0)\le\inf_{[0,1]}U+\varepsilon_j\), where \(\varepsilon_j\downarrow0\) and the window start has been relabeled zero. The same selection applies across a sequence of flows with the same \(S\), a common upper bound on \(U\) on their respective tails and \(\liminf J>1-o(1)\). One chooses the starting time in each tail after the moment lower bound holds. All estimates below are uniform in the chosen windows.

The identity bounds \(\delta_-\le C(M)\varepsilon_j\), while \(\int_0^1\delta=U(0)-U(1)\le\varepsilon_j\). Thus \(\int|\delta|\to0\), and a subsequence of \(b_j\) converges uniformly in time to a constant \(b_*\ge4\pi^2\). The \(L^2\) norm of the displayed square residual tends to zero. Also \(\int_0^1|J_j^2-1|\to0\). For large \(j\), the continuous quantity \(2c_j-b_j S\) cannot vanish on the window. Passing to a subsequence fixes its sign. Since \((J-1)^2\le|J^2-1|\) for \(J\ge0\), the scalar \((2c_j-b_jS)/4\) converges in \(L^2(0,1)\) to a fixed \(\mu=\pm b_*^{3/2}/4\). With \(\lambda=b_*/4>0\) the resulting actual force estimate is
\[
 f_j-\lambda K_j-\mu\longrightarrow0
       \quad\hbox{in }L^2((0,1)\times\mathbb S^1).
\]

## Compactness in a fixed spatial gauge

Parametrize each actual curve by fractional arclength, keeping the spatial origin at a fixed material label. Its tangential velocity in the normalized variables is \(w\), with
\[
 w_x=v-Kf,\qquad w(0)=0,\qquad
 K_\tau=-f_{xx}+(Kw)_x .
\]
Indeed the unscaled curve in these coordinates has velocity \(L(-fN+wT)\) with respect to \(\tau\), and \(|X_x|=L\). Differentiating this metric in time gives \(w_x=v-Kf\), since \(L_\tau=Lv\). Differentiating the unit tangent gives its angle velocity \(-f_x+Kw\), whose \(x\) derivative gives the last equation. All fields in these identities are spatially periodic, including for a nonzero turning number.

The force estimate and bounded \(b_j\) give a uniform \(L^2_{\tau,x}\) bound on \(f_j\). For each slice put \(X=\|K_{xx}\|_2\). Spatial integration by parts gives \(\|K_x\|_2^2\le\|K\|_2 X\). Starting where \(|K|^2\le b_j\) and integrating \((K^2)_x\) gives \(\|K\|_\infty^2\le C(1+\sqrt X)\). Hence
\[
 X\le\|f\|_2+\tfrac12\|K\|_\infty^2\|K\|_2
 \le\|f\|_2+C(1+\sqrt X).
\]
This bounds \(K_j\) in \(L^2_\tau H^2_x\). It also bounds \(\|K_j\|_\infty\) in \(L^8_\tau\). Since \(\|w\|_\infty\le 2\|K\|_2\|f\|_2\) and \(b_j\) is bounded, the curvature evolution bounds \(\partial_\tau K_j\) in \(L^2_\tau H^{-2}_x\).

It follows that a subsequence of \(K_j\) converges strongly in \(L^2_\tau H^1_x\). To see this directly, project onto the first \(N\) spatial Fourier modes. Each coefficient is bounded in \(H^1(0,1)\), and hence precompact in \(L^2(0,1)\). The discarded tail is \(O(1/N)\) in \(L^2_\tau H^1_x\), uniformly in \(j\), by the \(H^2\) bound. Denote the common limit by \(K\). After a further subsequence, \(\int K^2=b_*\) and \(\int K=S\) almost everywhere in time.

The forces converge strongly in \(L^2_{\tau,x}\) to \(f=\lambda K+\mu\). The cubic terms converge in \(L^1_{\tau,x}\), since \(K_j\to K\) in \(L^2_\tau L^\infty_x\) and \(\|K_j\|_{L^\infty_x}\) is bounded in \(L^8_\tau\). The products \(K_jf_j\) converge in \(L^1_{\tau,x}\), so \(v_j\to v=\lambda b_*+\mu S\) in \(L^1_\tau\), and \(w_j\to w\) in \(L^1_\tau L^\infty_x\). The bounds on \(K_j\) in \(L^\infty_\tau L^2_x\) and on \(w_j\) in \(L^2_\tau L^\infty_x\) give \(K_jw_j\to Kw\) in \(L^1_\tau L^2_x\). Passing to distributions in the two differential equations yields
\[
 K_{xx}=g(K),\quad g(y)=-y^3/2+\lambda y+\mu,\qquad
 K_\tau=-\lambda K_{xx}+(Kw)_x,\quad w_x=v-K(\lambda K+\mu).
\]
At almost every time, the same elliptic estimate now uses \(f=\lambda K+\mu\) whose spatial \(L^2\) norm is bounded uniformly in time. Hence \(K\in L^\infty_\tau H^2_x\). The equation \(K_{xx}=g(K)\) and spatial Sobolev multiplication give \(K\in L^\infty_\tau H^m_x\) for every integer \(m\). The fixed primitive defining \(w\) and the time equation give \(\partial_\tau K\in L^\infty_\tau H^m_x\) for every \(m\). Thus \(K\) is locally Lipschitz into each \(H^m\). The gauge equation gives \(w\) continuously as a function of \(K\). Substitution into the evolution yields continuous time derivatives, and iteration gives smoothness in the window interior.

## Compatibility over a time interval

Put \(H(y)=y(\lambda y+\mu)\), \(p(y)=-\lambda g(y)+(v-H(y))y\) and \(D_0=\partial_\tau-w\partial_x\). Then \(D_0 K=p(K)\) and \([D_0,\partial_x]=(v-H(K))\partial_x\). Differentiating \(K_{xx}=g(K)\) in time gives the identity
\[
 (p''-H')(K)K_x^2+
 \big(p'+2(v-H)\big)(K)g(K)-g'(K)p(K)=0 .
\]
At each fixed time a spatial first integral gives
\[
 K_x^2=-K^4/4+\lambda K^2+2\mu K+A
\]
for some spatial constant \(A\). Substitution in the preceding identity gives a polynomial in \(K\) of degree at most five. Its degree-five coefficient is \(9\lambda/4\). Indeed the three displayed terms contribute \(5\lambda/4\), \(7\lambda/4\) and \(-3\lambda/4\). A nonconstant continuous curvature takes an interval of values, which would force this polynomial to vanish identically. Since \(\lambda=b_*/4>0\), the curvature is constant. Consequently \(b_*=S^2\).

For a single flow the selected late slices therefore have curvature oscillation \(b-S^2\to0\). The positive lower bound on \(b_*\) gives \(S\ne0\). Restart at such a slice below the small-oscillation threshold and apply the circle stability theorem, after scaling to its stipulated length and reversing orientation if necessary. The two normal-speed conventions differ by a constant factor in time. [Andrews and Wheeler, Theorem 1](https://arxiv.org/html/2509.11129)

For the uniform gap, suppose that there were flows with a common tail cap \(M\), each without the asserted circular limit, with \(\liminf J>1-1/j\). The bounds \(S^2\le b\le2M\) and \(S\in2\pi\mathbb Z\) allow a subsequence with fixed \(S\). Apply the same window selection across these trajectories. The limit again satisfies \(b_*=S^2\ge4\pi^2\). For large \(j\), the original trajectory at the start of its selected window has curvature oscillation \(b_j(0)-S^2\) below the small-oscillation threshold for this fixed turning number. The same stability theorem forces each such trajectory to converge to a circle, contradicting the choice of flows. A turning-zero flow cannot converge to an immersed round circle. Since \(J=2G\) in that case, the stated bound on \(G\) follows. The general length-growth and half-plane migration questions remain open.

## Removing the energy cap

Write \(s_0=S/\sqrt{2U}\), \(h=c/b^{3/2}\), so \(J=|2h-s_0|\) and \(G=|h|\). Use the universal \(0<\epsilon<1/2\) from the static gap for the normalized signed cubic moment. This estimate implies that \(|s_0|\le\epsilon\) and \(G>1/2-\epsilon\) force the normalized dissipation \(e>\epsilon\), where \(U'=-(2U)^3L^{-4}e\) in physical time. The finite-interval estimate supplies one explicit choice of this \(\epsilon\); the uniform dynamical gap \(\eta(M)\) still follows by compactness. [Static gap and normalization](StrictHalfThreshold.md) · [Explicit estimate](FiniteWindowThreshold.md)

Suppose \(\liminf J>1-\epsilon/2\). On a sufficiently late tail we have \(J>1-\epsilon/2\). Whenever \(U\ge A_n=S^2/(2\epsilon^2)\), we have \(|s_0|\le\epsilon\), hence
\[
2G\ge J-|s_0|>1-3\epsilon/2>1-2\epsilon .
\]
It follows that \(U'<-\epsilon(2U)^3L^{-4}\) at each such time. The sign of the derivative at and above the barrier gives a global cap on \(U\) by a first-crossing argument. The quarter-power upper bound then gives \(\int^\infty L^{-4}dt=\infty\). If \(U\) stayed above \(A_n\) on the whole tail, integrating the differential inequality with \(2U\ge4\pi^2\) would contradict positivity of \(U\). Thus for \(S\ne0\) the trajectory enters \(U\le A_n\) in finite time and stays there. For \(S=0\) the inequality holds on the entire tail; the same contradiction rules out the assumed lower limit.

For \(n\ne0\) take \(\delta_n=\min\{\epsilon/2,\eta(A_n)\}\). The uniform gap for the cap \(A_n\) gives smooth circular convergence whenever \(\liminf J>1-\delta_n\). A smoothly converging normalized circle has \(K\to S\ne0\), hence \(J\to1\). Together with the turning-zero exclusion this proves that \(\liminf J\le1\) for every flow and characterizes equality.

## Formal verification

The Lean module `LengthGrowth.ActualFlow.AffineForceCompatibility` proves the spatial first integral and shows that its substitution in the time-compatibility polynomial forces a continuous curvature to be constant. The polynomial proof uses its fifth finite difference on six equally spaced curvature values. The theorem `spatially_constant_of_affine_force_evolution` derives this constraint from the affine force, the gauge equation and the divergence-form curvature evolution on an open time interval. Its proof uses joint smoothness to commute time and spatial derivatives. The finite-window selection, compactness, passage to the evolution equation in the limit, smoothness bootstrap, use of circle stability and centered-moment corollary without an energy cap are supplied by the mathematical proof above.
