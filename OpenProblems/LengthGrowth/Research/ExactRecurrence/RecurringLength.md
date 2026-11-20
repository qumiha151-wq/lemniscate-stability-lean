# Exact scale returns force two-sided fourth-root length growth

Let \(X(t)\) be a smooth regular closed plane free elastic flow in physical time \(t\ge0\), smooth up to its initial curve, with positive length \(L(t)\). Suppose slices at \(s<t_1\) coincide up to a plane similarity with spatial dilation factor \(r>0\) and a diffeomorphism of the parameter circle. All traversals of the immersed curve are retained.

Then \(r>1\) and there exist constants \(c_1,c_2>0\) such that, for every \(t\ge0\),
\[
 c_1(1+t)^{1/4}\le L(t)\le c_2(1+t)^{1/4}.
\]
The constants may depend on the solution and the return. In particular, a flow violating the proposed fourth-root upper bound cannot have even one exact similarity return.

## From a physical return to a scalar recurrence

The bending energy \(E=\tfrac12\int k^2ds\) is positive and scales by \(r^{-1}\). Its derivative is \(-\int F^2ds\), where \(F=k_{ss}+k^3/2\). The dilation variation gives \(\int F(X-c)\cdot N\,ds=-E\) for any constant \(c\), so \(F\) cannot vanish identically and \(E\) decreases strictly. Hence a later matching slice must have \(r>1\).

Write \(A=r^4\) and \(f(t)=A(t-s)+t_1\). If \(S\) is the matching spatial similarity, the flow \(S^{-1}X(f(t))\) obeys the same equation in \(t\) and matches \(X(t)\) at \(s\), up to a change of parameter. Forward uniqueness gives equality at least for \(t\ge s\). Thus even forward uniqueness alone gives the scalar result on the tail: \(T_*=(As-t_1)/(A-1)<s\), \(u=t-T_*>0\) there, and \(u_0=s-T_*>0\). With \(\ell(u)=L(T_*+u)\),
\[
     \ell(Au)=r\ell(u)\qquad(u\ge u_0).
\]
Positivity and continuity control the compact initial segment, so the claimed growth bounds on all \(t\ge0\) already follow. To see that the same recurrence itself extends to \(t=0\), use geometric backward uniqueness on the common physical interval of the two flows. The argument via normalized curvature and frequency quotients is given in [Exact covering multiplicity](CoveringRigidity.md). For two different trajectories, synchronize fractional arclength labels, orientation, tangent and position at the matching time. For each trajectory set \(d\tau=L^{-4}dt\), assigning \(\tau=0\) there. The normalized curvature difference satisfies the same fourth-order estimate used in that argument. Equality backwards of \(K\) determines the zero-mean tangential gauge, then \(L\) from \(L_\tau=v L\), physical time from \(t_\tau=L^4\), unit tangent from \(\partial_\tau T=(-f_{\rm el,x}+Kw)JT\), and position from \(\partial_\tau X=L(-f_{\rm el}JT+wT)\), with the notation of that note. On compact intervals the clocks are nonsingular. The equality therefore holds wherever both physical-time trajectories are defined. If \(T_*\ge0\), evaluating at the fixed point \(f(T_*)=T_*\) would give \(E(T_*)=E(T_*)/r\), contradicting positivity. Hence \(T_*<0\), and one may take \(u_0=-T_*\).

## Fundamental interval

The positive continuous function \(g(u)=\ell(u)^4/u\) satisfies \(g(Au)=g(u)\). Let \(c,C\) be its positive minimum and maximum on \([u_0,Au_0]\). For \(u\ge u_0\), choose \(n\ge0\) with \(A^n\le u/u_0<A^{n+1}\). Then \(v=u/A^n\in[u_0,Au_0]\) and iteration gives \(g(u)=g(v)\). Thus \(cu\le \ell(u)^4\le Cu\) on the tail. Since \((t-T_*)/(1+t)\) stays between two positive finite constants on \(t\ge s\), taking positive fourth roots and extending across the compact interval \(0\le t\le s\) proves the result.

The Lean module \(\texttt{LengthGrowth.ActualFlow.RecurringLength}\) proves the scalar implication from a continuous positive length and the exact recurrence for \(u\ge u_0>0\) to the fourth-power bounds on that entire tail. Geometric uniqueness, physical similarity scaling and the passage from a pair of matching slices to the recurrence are mathematical arguments. This does not settle length growth along trajectories without returns. [Miura and Wheeler, Section 1](https://arxiv.org/abs/2404.12619)
