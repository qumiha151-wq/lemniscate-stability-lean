# A critical saturating flow must have divergent mean fourth curvature moment on every macroscopic time window

Let \(F=k_{ss}+k^3/2\), \(E=\int k^2ds/2\), \(U=EL\), \(\eta=LU'/E^3\), and \(\rho=1/2-\eta\) on a smooth closed planar free elastic flow. Write \(\langle f\rangle=L^{-1}\int f\,ds\). For a sequence of such flows use the initial RMS dilation \(m_j=\sqrt{2E_j(0)/L_j(0)}\) of space with time dilated by \(m_j^4\). In the following implication all variables are in these initially normalized units. For every fixed \(T>0\),
\[
 U_j(0)\longrightarrow\infty,\quad
 \int_0^T\rho_j\,dt\longrightarrow0
 \quad\Longrightarrow\quad
 \int_0^T\langle k_j^4\rangle\,dt\longrightarrow\infty.                \tag{1}
\]
The conclusion \(\int\langle k^4\rangle\,dt\) is unchanged by a fixed parabolic dilation of the window. In particular, for a single genuine flow with the two matched leading laws
\[
 L(t)\sim\ell t^{1/3},\qquad E(t)\sim(\ell/\sqrt3)t^{-1/6},
\]
every \(c>0\) satisfies
\[
                 \int_t^{(1+c)t}\langle k(r)^4\rangle\,dr
                    \longrightarrow\infty.                            \tag{2}
\]
On these same physical windows both time integrals of \(\langle k_s^2\rangle\) and \(\langle k^4\rangle/2\) diverge, and the second minus the first tends to \(\log(1+c)/3\).
No decay rate of the relative errors and no derivative bounds are assumed. A diverging fourth moment can be carried by a small arclength set. These conditions do not rule out the two leading laws.

## Choosing a material origin that stays representative

Suppose after extraction that the left hypotheses of (1) hold and \(\int_0^T\langle k^4\rangle dt\le C\). Let \(P=L(0)=\sqrt{2U(0)}\), \(\lambda=E/(2L)\), \(R=F-\lambda k\), \(\mu=L'/L\). The square completion gives \(\langle R^2\rangle=8\lambda^3\rho\), \(\langle k^2\rangle=4\lambda\). The energy and length equations give
\[
 (\lambda^{-2})'=12+O(\sqrt\rho+\rho),\qquad
 \mu=4\lambda^2+O(\lambda^2\sqrt\rho).
\]
As \(\lambda(0)=1/4\), it follows that \(\lambda\to\lambda_*=(16+12t)^{-1/2}\) uniformly and \(\mu\to4\lambda_*^2\) in \(L^2\). In particular all \(L(t)/P\) are bounded above and away from zero and \(\int_0^T\langle R^2\rangle\,dt=o(1)\). Periodic integration by parts gives
\[
        \langle k_s^2\rangle
         =\tfrac12\langle k^4\rangle-\lambda\langle k^2\rangle
              -\langle kR\rangle .
\]
The spacetime mean of \(k_s^2\) is therefore bounded. Choose \(b_j\in[T/4,T/2]\) with both \(\langle k^4\rangle\) and \(\langle k_s^2\rangle\) bounded, and extract \(b_j\to b\). At this time \(\langle k^2\rangle\ge c>0\). Cauchy–Schwarz and the fourth-moment bound give constants \(a,d>0\) such that the initial arclength fraction with \(|k|\ge a\) is at least \(d\).

Use arclength \(\xi\) at time \(b_j\) as a material label and write \(g(t,\xi)d\xi=ds(t)\) on \(b_j\le t\le b_j+T/4\). Then \(g(b_j,\xi)=1\) and \(g_t=kFg\). Pointwise \((kF)_-\le R^2/(4\lambda)\), by completing the square in \(k\). Thus the set of labels where \(g\) ever falls below \(1/2\) has initial measure \(o(P)\). Indeed each such label consumes at least \(1/2\) of \(\int (g_t)_-dt\), and the integral of this quantity over labels is at most \(C\int\int R^2ds\,dt=o(P)\). Denote the remaining labels by \(G_j\). At every subsequent time, the image of \(d\xi|_{G_j}\) under passage to current arclength is bounded above by \(2\,ds\).

For an origin \(\xi\in G_j\) use current arclength about that material point, divided by \(h(t)=L(t)/L(b_j)\), as coordinate \(x\). Then \(ds=h(t)dx\), with \(h,h^{-1}\) uniformly bounded. For any nonnegative spacetime integrand \(f\),
\[
 \frac1{L(b_j)}\int_{G_j}
  \int_{b_j}^{b_j+T/4}\int_{-4}^4 f(t,x;\xi)\,dx\,dt\,d\xi
 \le C\int_{b_j}^{b_j+T/4}\langle f\rangle\,dt.                      \tag{3}
\]
The bound follows from the preceding domination and Fubini on each periodic time slice. The initial-time counterpart also holds, with \(g=h=1\). Use (3) for \(k_s^2+k^4\), for \(R^2\), and the initial counterpart for \(k_s^2\). Markov's inequality, with large fixed thresholds on the bounded averages and a threshold tending to zero for \(R^2\), excludes less than \(dL(b_j)/2\) further labels for all sufficiently large \(j\). Since the complement of \(G_j\) has fraction \(o(1)\), choose an origin with \(|k(b_j,0)|\ge a\), bounded initial local squared slope integral, bounded local \(\int(k_s^2+k^4)dx\,dt\), and vanishing local \(\int R^2dx\,dt\). The initial squared slope bound and the fundamental theorem of calculus give a fixed small interval about \(0\) where \(k\) has one sign and magnitude at least \(a/2\). After extraction its sign is the same for all \(j\).

## Local spacetime limit

Shift time by \(b_j\). After extraction the global coefficients now converge to the translated \(\lambda_*(b+t), 4\lambda_*^2(b+t)\), and \(h\) converges uniformly to the solution of \(h_*'=4\lambda_*^2 h_*\), \(h_*(0)=1\). For readability use \(\lambda_*\) for the translated limit. At the material origin the tangential velocity \(\alpha\) in the constant-speed coordinate is zero. In this gauge the actual equations are
\[
 \alpha_x=h(\mu-kF),\qquad
 (hk)_t=-h^{-1}F_{xx}+(\alpha k)_x,\qquad h^{-2}k_{xx}=F-k^3/2 .
\]
Split \(\alpha=\alpha^0+\alpha^1\) by integrating \(h(\mu-\lambda k^2)\) and \(-hkR\), respectively, from \(0\) to \(x\). By the selected local bounds, \(\alpha^0\) is bounded in \(L^2_t L^\infty_x\), and
\[
 \|\alpha^1\|_{L^{4/3}_tL^\infty_x}
       \le C\|k\|_{L^4_{t,x}}\|R\|_{L^2_{t,x}}\to0 .
\]
In particular \(\alpha^0k\) is bounded in \(L^{4/3}_t L^1_x\), \(\alpha^1 k\to0\) in \(L^1_{t,x}\), and \(F=\lambda k+R\) is bounded in \(L^2_{t,x}\). The selected slope and curvature bounds give local boundedness of \(hk\) in \(L^2_tH^1_x\). On each smaller interval its time derivative is bounded in \(L^1_tH^{-2}_x\) by the conservative equation, since in dimension one \(H^2\) controls the supremum of the first derivative. Localizing strictly inside the interval and applying time-derivative compactness gives strong local \(L^2_{t,x}\) convergence of \(k\) to \(K\); interpolation gives the same in every \(L^p\) for \(p<4\). For a smooth nonnegative test supported in the fixed initial sign interval, the pairing with \(hk\) is bounded away from zero at time zero. Its change over any time increment of length \(\delta\) is at most \(C(\delta^{1/2}+\delta^{1/4})+o(1)\) by the displayed bounds. Thus \(K\) is nonzero on the interior in spacetime.

Strong \(L^3\) convergence gives \(\alpha^0\to\alpha_*=h_*\int_0^x(4\lambda_*^2-\lambda_*K^2)dw\) in \(L^{3/2}_tL^\infty_x\), and \(\alpha^0 k\to\alpha_*K\) in \(L^1_{t,x}\). Passing to both equations yields, with \(\partial_s=h_*^{-1}\partial_x\),
\[
 K_{ss}=\lambda_*K-K^3/2,\qquad
 \partial_t(h_*K)=-h_*^{-1}(\lambda_*K)_{xx}+(\alpha_*K)_x .
\]
Initially the limiting fourth moment bound is local \(L^4_{t,x}\). For almost every time the spatial ODE makes \(K\) smooth. Its first integral \(J=K_s^2+(K^2/2-\lambda_*)^2\) is spatially constant. On a fixed interior \(x\)-interval take smooth nonnegative \(\phi\) of integral one. Integration by parts in the spatial ODE gives
\[
 \int\phi K_s^2dx =
 \frac1{2h_*^2}\int\phi''K^2dx-\lambda_*\int\phi K^2dx
                  +\tfrac12\int\phi K^4dx .
\]
Consequently \(J(t)\le C(1+\int_{\mathrm{supp}\,\phi}K^4dx)\). This upgrades \(\|K\|_{\infty,x}\) to \(L^4_t\) and \(\|K_s\|_{\infty,x}\) to \(L^2_t\) on every smaller interval. The spatial ODE and the two conservation equations now give \(\partial_tK=\alpha_*K_s-\lambda_*^2K-\lambda_*K^3/2\) with right side in \(L^1_t C_x\). On nested interior intervals this gives a continuous spacetime representative, then continuous spatial derivatives by the spatial ODE and difference quotients. Differentiating these equations upgrades to smoothness there, as detailed in the [macroscopic deficit proof](MacroscopicDeficitBudget.md).

On this nonzero smooth patch \(F=\lambda_*K\). The actual material derivative \(D_t=\partial_t-\alpha_*\partial_s\) satisfies \([D_t,\partial_s]=-\lambda_* K^2\partial_s\). The compatibility calculation in the [RMS saturation note](MacroscopicSaturation.md) forces a nonzero patch to have \(K^2=2\lambda_*\) and \(\lambda_*'=-4\lambda_*^3\). The scalar energy and length limit gives \(\lambda_*'=-6\lambda_*^3\). This contradiction proves (1).

## Physical dyadic windows at critical growth

Under the two matched leading laws the remaining length-normalized clock \(\delta(t)=\int_t^\infty L^{-4}dr\) satisfies \(U(t)\sqrt{\delta(t)}\to1\). Hence
\[
 2\int_t^\infty \rho(r)L(r)^{-4}\,dr
       =\delta(t)-U(t)^{-2}=o(t^{-1/3}).
\]
For any fixed \(c>0\), this gives \(\int_t^{(1+c)t}\rho(r)dr=o(t)\). Here \(m(t)^4\sim 4/(3t)\) and \(U(t)\to\infty\). After a fixed dilation at each starting time this physical interval contains a fixed positive RMS duration and its normalized integral of \(\rho\) tends to zero. Apply (1) on that duration and use the exact dilation invariance of \(\langle k^4\rangle\,dt\). This proves (2).

Indeed, periodic integration of \(kF\) gives \(\mu=\langle k^4\rangle/2-\langle k_s^2\rangle\). Its integral on this window tends to \(\log(1+c)/3\) by the assumed length law. The geometric input behind this cancellation is the divergence of each term in (2).

These are written arguments. The material energy and length variations and the geometric stress estimates used in the preceding work are individually formalized. The choice of representative origins, the limit in (1), and the implication (2) have no Lean verification.
