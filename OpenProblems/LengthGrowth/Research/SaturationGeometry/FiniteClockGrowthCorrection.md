# The minimal finite-clock blow-up profile has an unbounded additive correction

Let \(X(t)\) be a single smooth global closed planar free elastic flow, \(L\) its length, \(E\) its bending energy, \(U=EL\), and \(\tau(t)=\int_0^tL^{-4}\,dt\). Suppose the terminal value \(\tau_*=\tau(\infty)\) is finite. Then
\[
 \boxed{\quad
 U(\tau)-\frac1{\sqrt{\tau_*-\tau}}\ \longrightarrow\ +\infty .
 \quad}                                                               \tag{1}
\]
In particular the previously established lower bound \(U\ge(\tau_*-\tau)^{-1/2}\) cannot have an additive bounded remainder, even along a sequence of late times. This is a necessary condition on finite-clock solutions. Existence of such a solution and the general fourth-root upper growth bound remain open.

Write \(\eta=LU_t/E^3,\ \rho=1/2-\eta,\ B=U\rho\). Cauchy–Schwarz gives \(\rho\ge0\), and \(U_\tau=\eta U^3\). Finite clock implies \(U\) is unbounded since bounded \(U\) would give \(L=O((1+t)^{1/4})\) by the energy–length equivalence. The inequality \((U^{-2})_\tau\ge-1\) and a sequence of arbitrarily large products approaching \(\tau_*\) give \(U(\tau)^{-2}\le\tau_*-\tau\); in particular \(U\to\infty\). Integrating the exact equation now yields
\[
 A(\tau):=\tau_*-\tau-U(\tau)^{-2}
       =2\int_\tau^{\tau_*}\rho(\sigma)\,d\sigma .                    \tag{2}
\]

In fact \(A(\tau)/(\tau_*-\tau)^{3/2}\to+\infty\). If this failed, choose \(\tau_j\uparrow\tau_*\) with \(A(\tau_j)\le C\delta_j^{3/2}\), \(\delta_j=\tau_*-\tau_j\). On \(I_j=[\tau_j,\tau_j+\delta_j/2]\), (2) gives
\[
 0\le \tau_*-\sigma-U(\sigma)^{-2}\le C\delta_j^{3/2},\qquad
 \int_{I_j}\rho\,d\sigma\le C\delta_j^{3/2}/2 .
\]
Thus \(c\delta_j^{-1/2}\le U(\sigma)\le C_1\delta_j^{-1/2}\) throughout \(I_j\), with universal constants for large \(j\).

Put \(m(t)^2=2E(t)/L(t)=4\lambda(t)\), and use the moving RMS clock \(d\theta=m(t)^4\,dt=4U^2d\tau\). The \(\theta\)-duration of \(I_j\) is bounded above and bounded away from zero. Also
\[
 \int_{I_j}B\,d\theta=4\int_{I_j}U^3\rho\,d\sigma\le C_2,\qquad
 \int_{I_j}\rho\,d\theta=4\int_{I_j}U^2\rho\,d\sigma=O(\delta_j^{1/2}).
\]
The physical energy and length identities give \((\lambda^{-2})_t=12+O(\sqrt\rho+\rho)\), hence
\(\left|(\log\lambda)_\theta\right|\le C(1+\sqrt\rho+\rho)\). By integration and Cauchy–Schwarz, \(m(t)/m(t_j)\) and its reciprocal are uniformly bounded throughout \(I_j\). Here \(t_j\) is the physical time with \(\tau(t_j)=\tau_j\). The fixed initial RMS measure \(m(t_j)^4dt\) and \(d\theta\) are therefore comparable with constants independent of \(j\). In particular \(I_j\) contains a fixed positive forward duration in the initial RMS units of each \(t_j\), during which the integral of \(B\) in those units stays bounded. This contradicts the [macroscopic physical deficit theorem](MacroscopicDeficitBudget.md), since \(U(t_j)\to\infty\).

Finally, putting \(\delta=\tau_*-\tau\) gives
\[
 \frac{A(\tau)}{\delta^{3/2}}
 =\left(U-\delta^{-1/2}\right)
       \frac{U\sqrt\delta+1}{U^2\delta}
 \le 2\left(U-\delta^{-1/2}\right)
\]
because \(U\sqrt\delta\ge1\). This proves (1).

## A forward estimate without assuming a finite terminal clock

Fix \(0<a<1\). Let a sequence of initial slices, possibly on distinct flows, have \(H_j=U_j(\tau_j)\to\infty\). Then
\[
 \frac{H_j}{\sqrt{1-a}}-
 U_j\!\left(\tau_j+\frac{a}{H_j^2}\right)\longrightarrow+\infty.       \tag{3}
\]
This includes the case of an infinite length-normalized clock. In the finite-clock case the time on the right is available by the already proved bound \(H_j^{-2}\le\tau_*-\tau_j\). The scalar inequality \(U_\tau\le U^3/2\) gives the nonnegativity of (3). If the difference remained bounded on a subsequence, then at its right endpoint \(U^{-2}=(1-a)/H_j^2+O_a(H_j^{-3})\). Integrating \((U^{-2})_\tau=-1+2\rho\) would give \(\int\rho\,d\tau=O_a(H_j^{-3})\) on the forward interval. On all prefixes the same integral is nonnegative and no larger; the exact identity consequently gives \(c_aH_j\le U\le C_aH_j\) throughout. This interval has a moving RMS duration bounded above and below independently of \(j\), and \(\int B\,d\theta\) stays bounded. The comparison to initial RMS units above gives the same contradiction. Thus (3) excludes additive bounded errors in the scalar forward growth envelope on high records for either clock.

For one example in physical time, the two asymptotic laws
\[
 L(t)=\ell\,t^{1/3}(1+O(t^{-1/6})),\qquad
 E(t)=\frac{\ell}{\sqrt3}\,t^{-1/6}(1+O(t^{-1/6})),\qquad \ell>0,
\]
cannot hold simultaneously. They would give
\(\tau_*-\tau(t)=3\ell^{-4}t^{-1/3}(1+O(t^{-1/6}))\), and the two leading terms in (1) would agree up to \(O(1)\). This consequence concerns both leading coefficients and the stated remainder. The exponent \(1/3\) by itself has not been ruled out. Formula (1) and its physical consequence are analytic results, without Lean verification.
