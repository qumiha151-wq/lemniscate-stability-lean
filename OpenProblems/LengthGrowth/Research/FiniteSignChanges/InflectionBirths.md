# Inflection pairs on a closed free elastic flow at vanishing time and energy cost

There is a smooth embedded convex closed curve of turning number one whose initial signed curvature has no changes of sign and whose free elastic flow satisfies
\[
 \lim_{t\downarrow0} N(t)=+\infty .
\]
Here \(N(t)\) counts genuine sign changes of the signed curvature on the material circle, allowing \(+\infty\). The assertion also holds when counting only simple zeros at time \(t\). The initial length can be fixed to \(2\pi\) and the initial curvature oscillation \(L\int(k-2\pi/L)^2 ds\) can be made arbitrarily small. In particular this phenomenon occurs on flows which ultimately converge smoothly, after length normalization, to the once-covered circle.

## A closed initial curve

Work on an arclength circle \(s\in\mathbb R/(2\pi\mathbb Z)\). First define a nonnegative smooth \(\pi\)-periodic function \(q\). On a small neighborhood \(|s|<d\) of zero set
\[
 q(s)=e^{-1/s^2} H(s^{-4}),\qquad H(y)=1-\cos y+(1-\cos y)^2,\qquad q(0)=0 .
\]
Take \(q=1\) outside \(|s|<2d\) in a fundamental period. On the intervening region use a smooth convex combination of these formulas with a cutoff constant near both boundaries. Smoothness at zero follows because every derivative of the oscillatory factor grows at most polynomially in \(1/|s|\). For sufficiently small \(d\), \(0\le q\le1\), and \(q\) is positive on a dense open set.

Let \(c=\pi/\int_0^\pi q(s)ds\), \(k=cq\), \(\theta(s)=\int_0^s k(\sigma)d\sigma\) and
\(X(s)=\int_0^s(\cos\theta,\sin\theta)d\sigma\).
Then \(\theta(s+\pi)=\theta(s)+\pi\). Hence \(X\) is closed of length \(2\pi\) with actual signed curvature \(k\). The tangent angle is strictly increasing, as every nonempty interval has positive curvature somewhere. To check embedding and convexity directly, fix any \(s_0\) and let \(N_0\) be its left unit normal. The signed height \(\langle X(s)-X(s_0),N_0\rangle\) starts at zero, strictly increases on \((s_0,s_0+\pi)\), and strictly decreases thereafter, ending again at zero at \(s_0+2\pi\). This follows from its derivative \(\sin(\theta(s)-\theta(s_0))\). Each tangent line supports the curve and meets it only once. Finally \(c=1+O(d)\) and \(\int_0^{2\pi}(k-1)^2 ds=O(d)\). Taking \(d\) sufficiently small places the curve in the single-turn stability regime of [Andrews and Wheeler, Theorem 1](https://arxiv.org/abs/2509.11129).

## Splitting of the curvature minima

Choose the centers \(s_j=(2\pi j)^{-1/4}\) lying in \((0,d)\). Write \(a=e^{-1/s^2}\), \(v=s^{-4}\). At these centers \(H=H'=H'''=0\), \(H''=1\), \(H''''=5\). Therefore \(q=q'=0\), \(q''=a(v')^2>0\), and
\[
 q'''' = a\{5(v')^4+3(v'')^2+4v'v'''\}
                  +12 a' v'v''+6a''(v')^2.
\]
The leading term is \(5a(v')^4\), of order \(a s^{-20}\). All other terms have order \(O(a s^{-16})\) or smaller as \(s\downarrow0\). Consequently \(k''''(s_j)>0\) for all sufficiently large \(j\).

On a smooth normal free elastic flow the material curvature satisfies
\[
 k_t=-F_{ss}-k^2 F,\qquad F=k_{ss}+k^3/2.
\]
At a marked zero on the initial slice this gives \(k_t(0,s_j)=-k_{ssss}(0,s_j)<0\). Here the initial material label is arclength. A tangential velocity would add a term proportional to \(k_s\), which also vanishes at the center. For each \(j\), take a small closed interval about \(s_j\) whose endpoints have positive initial curvature and throughout which the second derivative with respect to its initial material coordinate is positive. Take these intervals mutually disjoint. Continuity preserves the endpoint signs and strict second-derivative bound for sufficiently small times depending on \(j\). At the original center the curvature is strictly negative at all sufficiently small positive times. Strict convexity of the curvature function in this fixed coordinate gives two simple curvature zeros of opposite crossing directions on that interval. For any finite selection of \(m\) centers all these conclusions hold throughout a common time interval \((0,t_m)\). Thus \(N(t)\ge2m\) for all \(0<t<t_m\), proving the claimed limit.

The energy identity \(E(0)-E(t)=\int_0^t\int F^2 ds\,du\) gives vanishing energy expenditure as \(t\downarrow0\). Smoothness up to the initial slice bounds all fixed orders of curvature derivatives on the same slab. In particular there is no positive per-pair lower bound on the elapsed time measured in units of \(E(0)^{-4}\), or on the relative decrease of energy, applying to raw inflection births on all smooth flows. The widths and turning angles of the newborn lobes shrink to zero. Estimates requiring a fixed lobe turning remain applicable to their stated class. Eventual finiteness of the sign-change count, positive limiting bending energy and the unrestricted quarter-power length question remain open.

For initial curvature strictly positive everywhere, there is a finite version. For a given \(m\), choose \(t<t_m\) with the prescribed dimensionless time and energy loss as small as desired. Replace \(q\) by \(q+\delta\), recompute \(c\) and \(X\) as above, and let \(\delta\downarrow0\). Smooth dependence for the fourth-order parabolic initial value problem, using a strictly parabolic parametrization on a common short time interval, preserves the finitely many strict signs at the marked centers and interval endpoints at this fixed \(t\), and it preserves small energy loss. Thus at least \(2m\) changes of sign arise from strictly positive initial curvature in the prescribed budgets. The construction of the single weakly positive curvature flow and its simple zeros uses only smooth existence, the curvature equation, and continuity. See [Miura and Wheeler, Theorem 1.1](https://arxiv.org/html/2404.12619v3#S1) and the parabolic formulation in [Mantegazza, Pluda and Pozzetta](https://arxiv.org/abs/2009.12870).
