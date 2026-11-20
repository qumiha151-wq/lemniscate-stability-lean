# Simultaneous appearance of large alternating curvature arcs at small dissipation

Fix any integer \(N\ge8\). There exist smooth closed free elastic flows of turning number one, and positive times arbitrarily short in the local curvature scale, with the following two properties. Initially **every** one-sign curvature arc between genuine sign changes has total absolute turning less than \(1/8\). At the later time there are at least \(4N\) cyclically alternating positive and negative arcs, each with absolute turning greater than \(1/4\). Their peak absolute curvatures have sum at least a universal positive multiple of the initial energy. The energy loss divided by the initial energy can be made arbitrarily small. Whole-curve dilation can fix the initial energy to one.

## Initial positions and the short-time sign computation

Use material arclength \(s\in\mathbb R/(2\pi\mathbb Z)\) on the initial slice. Fix \(M=200\), let \(\omega=2N\), \(m=2MN\), and prescribe
\[
 B(s)=1+N\cos(\omega s),\qquad
 k_\varepsilon(s)=B(s)\,[1-(1+\varepsilon)\cos(ms+\phi)] .
\]
For \(0\le\varepsilon<1\), this function is \(\pi\)-periodic with mean one by trigonometric orthogonality (\(M>1\)). Integrate \(\theta'=k_\varepsilon\), \(X'=(\cos\theta,\sin\theta)\). Then \(X'(s+\pi)=-X'(s)\), proving exact position closure and turning number one. Choose a phase \(\phi\) for which the zeros of \(B\) avoid \(\cos(ms+\phi)=1\). For sufficiently small \(\varepsilon>0\) the two zero sets remain disjoint, every zero is simple, and the \(m\)-harmonic factor takes both signs. Successive zeros of that factor have separation at most \(2\pi/m=\pi/(MN)\). Thus every one-sign arc has length at most \(\pi/(MN)\) and turning at most \(3(N+1)\pi/(MN)<1/8\).

First take \(\varepsilon=0\). Use the \(4N\) pairwise disjoint closed intervals centered alternately on the maxima and minima of \(\cos(\omega s)\) where \(|\cos(\omega s)|\ge1/2\) with that center's sign. Each has length \(\pi/(3N)\). Write \(\sigma=\operatorname{sign}(B)\) on one of these intervals. At initial time \(\sigma k_0\ge0\), and its angular mass is at least
\[
 (N/2-1)\left[\pi/(3N)-2/m\right]>1/4 .
\]
Indeed \(\int_I\cos(ms+\phi)\) has absolute value at most \(2/m\), and the other bracket in \(k_0\) is nonnegative. The minimum of the displayed lower bound for \(N\ge8\) is attained at \(N=8\).

At any of the finitely many zeros of \(k_0\) on such a closed interval, the oscillatory bracket and its first and third derivatives vanish, while its second derivative is \(m^2\) and its fourth derivative is \(-m^4\). Hence
\[
 k_0''''=-m^4 B+6m^2 B'',\qquad B''=-\omega^2(B-1).
\]
Since \(B\) and \(B-1\) have the same sign on these intervals, \(\sigma k_0''''<0\). The actual normal free elastic flow gives \(k_t=-F_{ss}-k^2F\), \(F=k_{ss}+k^3/2\). At each marked zero this gives \(\sigma k_t=-\sigma k_0''''>0\). On a small fixed material neighborhood of that zero it remains positive for a common short time by smoothness. On the remaining compact parts of the chosen intervals \(\sigma k_0\) has a positive lower bound. Combining these facts over all finite intervals shows that their entire curvatures have their strict designated signs at every sufficiently small positive time. Angular mass on fixed material arcs is continuous in time, so each remains above \(1/4\). The signs alternate, so all \(4N\) arcs belong to distinct maximal sign leaves.

For each group choose also a point near the center of its interval with \(\cos(ms+\phi)=-1\), within distance \(\pi/m\) of the center. There \(\sigma k_0\ge N-2\). This bound is deliberately weak, since \(\cos(\pi/M)>1/2\). Continuity in time, then in the data, ensures that each group contains a point with \(|k|\ge N/2\) for the times and positive perturbations under consideration. The initial energy satisfies \(E(0)\le9\pi (N+1)^2\) from the uniform pointwise bound. Thus the sum of the \(4N\) selected peaks is at least \(2N^2\), a universal fraction of \(E(0)\).

Choose a sufficiently small fixed positive time \(t\) on the \(\varepsilon=0\) flow. By smooth dependence on the initial immersion the finite interval signs, angles and peaks at this time persist for all sufficiently small \(\varepsilon>0\) in a common parametrization. The energy difference also depends continuously on the data. Since \(E(0)-E(t)=\int_0^t\int F^2 ds\,dr\to0\) on the unperturbed smooth flow, \(t\) and then \(\varepsilon\) can be chosen to make both \(E(0)^{-1}(E(0)-E(t))\) and \(tN^4\) as small as desired. The marked peaks are comparable to \(N\) by continuity and the initial uniform bound. Under a spatial dilation by \(\lambda\) energy and peak curvature both scale by \(\lambda^{-1}\) and time by \(\lambda^4\). These relative statements therefore hold at initial energy one as well. For continuous dependence at this step, write nearby parametrized immersions locally as normal graphs over the unperturbed initial immersion, after reparametrization on the parameter circle. The principal part of the scalar graph equation is \(-|X_s|^{-4}u_{ssss}\) with smooth lower-order terms. Its leading coefficient stays uniformly parabolic for nearby regular graphs. Continuous dependence on that common short time interval follows from the closed-manifold parabolic theorem. The strict signs, turning integrals, energy and peaks are invariant under reparametrization. [Mantegazza and Martinazzi, Theorem 1.1](https://www.numdam.org/item/ASNSP_2012_5_11_4_857_0/) · [Miura and Wheeler, Theorem 1.1](https://arxiv.org/html/2404.12619v3#S1)

## Implication for a long-time birth argument

A dissipation lower bound proportional to the sum of terminal peak curvatures of all newly counted alternating angular groups fails even with the separated thresholds \(1/8\) and \(1/4\) and with arbitrarily short evolution. Each terminal arc inherited its signed turning from a long interval on which the initial angle already had a substantial net change. Tiny opposite-sign gaps had divided it into short one-sign pieces. Their disappearance reveals this stored turning.

Counting disjoint ordered *material intervals* with alternating net signed turning would detect that turning already at the initial time. For the genuine normal flow and fixed material endpoints \(a,b\), the exact change in their lifted tangent-angle difference is \(\int_0^t[F_s(a,r)-F_s(b,r)]dr\). A global estimate paying for new large net changes, or for increases in the weighted peak mass of pre-existing groups, would require control of this temporal transport. The example treats one early interval for each initial curve and provides no trajectory with super-quarter-power growth or positive limiting energy.
