# A growing deficit budget on every fixed RMS time window

Let \(F=k_{ss}+k^3/2,\ E=\tfrac12\int k^2ds,\ L=\int ds,\ U=EL,\ \eta=LU'/E^3\) on a true smooth free elastic flow of a closed planar immersion. Set \(B=U(1/2-\eta)\). For any sequence of such flows and any fixed \(T>0\), put \(m_j=(2E_j(0)/L_j(0))^{1/2}\). Then
\[
 U_j(0)\longrightarrow\infty
 \quad\Longrightarrow\quad
 m_j^4\int_0^{T/m_j^4}B_j(t)\,dt\longrightarrow\infty .             \tag{1}
\]
Starting times can be chosen independently, so this applies to the successive high records of a single trajectory. There is no bound on the initial derivatives, length, turning number, or covering number in this assertion. The conclusion excludes staying within \(O(1/U)\) of the maximal growth rate in *time average* throughout a fixed root-mean-square curvature window. A sequence with \(\eta\) positive and bounded away from its maximum can satisfy (1).

All following coordinates use the fixed initial spatial dilation \(m_j\) and the associated physical time \(m_j^4 t\); the initial RMS curvature is one. Suppose to the contrary that \(\int_0^T B_j(t)\,dt\le C\) on a subsequence. Write \(H_j=U_j(0)\to\infty,\ P_j=L_j(0)=\sqrt{2H_j}\), and omit indices where no confusion arises.

## Total residual and geometric bounds

Set \(\lambda=E/(2L),\ \rho=1/2-\eta,\ R=F-\lambda k,\ D=\int F^2ds\). The exact physical identities give
\[
 \|R\|_2^2=\frac{E^3}{L^2}\rho=\frac{4\lambda^2 B}{L},\quad
 \frac{L'}{L}=4\lambda^2+O(\lambda^2\sqrt\rho),\quad
 \frac{D}{E}=2\lambda^2+O(\lambda^2(\sqrt\rho+\rho)).
\]
The error bounds follow by expanding \(D\) and \(L'=\int kF\) and using \(\int k^2=2E\). Hence \((\lambda^{-2})'=12+O(\sqrt\rho+\rho)\), and \((\log U)'=4\lambda^2(1/2-\rho)\).

Initially \(\lambda(0)=1/4\). Until the first potential fall of \(U\) to \(H/2\), \(\int\rho\le2C/H\). Integrating the \(\lambda^{-2}\) identity gives uniform convergence on the stopped intervals to \(16+12t\), since \(\int\sqrt\rho\le\sqrt{T\int\rho}\). Thus \(\log[U(t)/H]\ge-C_T\int\rho=o(1)\) on those intervals. The stopping value cannot occur for large \(j\). On the whole window, \(\lambda_j\to\lambda_*=(16+12t)^{-1/2}\) uniformly, \(\mu_j=L_j'/L_j\to4\lambda_*^2=\mu_*\) in \(L^2(0,T)\), and \(h_j=L_j/P_j\) converges uniformly to \(h_*=\exp\int_0^t\mu_*\). The \(h_j\) and their reciprocals are bounded uniformly. In particular
\[
 \int_0^T\!\!\int R_j^2\,ds\,dt=O(P_j^{-1}).
                                                               \tag{2}
\]

The elastic stress corrected for \(\lambda k\) is \(W=(k^2/2-\lambda)T+k_s N\), with \(W_s=RN\). It has spatial oscillation at most \(\int|R|\le2\lambda\sqrt B\). Writing angular brackets for the instantaneous arclength average and \(M=\|k\|_\infty\), integration by parts gives
\[
 \langle|W|^2\rangle=\tfrac34\langle k^4\rangle-2\lambda\langle k^2\rangle+\lambda^2-\langle kR\rangle
 \le C_T(1+M^2+\sqrt B).
\]
Indeed \(\langle k^2\rangle=4\lambda\) and \(|\langle kR\rangle|\le C_T\sqrt B/L\). Some point has \(|W|\le\langle|W|^2\rangle^{1/2}\). At a curvature maximum \(M^2/2-\lambda\le|W|\), so the oscillation bound implies \(M^2\le C_T(1+M+\sqrt B)\). Combining this with the same bound for \(\sup|W|\) yields
\[
 \|k\|_\infty^4+\|k_s\|_\infty^2\le C_T(1+B)
                                                               \tag{3}
\]
pointwise in time. Thus these two spatial norms are bounded, respectively, in \(L_t^4\) and \(L_t^2\) along the sequence.

## Choice of moving origins

Choose \(t_j\in[T/3,2T/3]\) with \(B_j(t_j)\le 3C/T\), and at that time choose a material label where \(|k_j|\ge\sqrt{4\lambda_j(t_j)}\). Give the entire parameter circle this moving material origin. Use a constant-speed coordinate \(x\) of period \(P_j\), with \(ds=h_j(t)dx\). It is constructed by signed arclength from the origin at the given time divided by \(h_j(t)\). The tangential velocity in this gauge, denoted by \(\alpha_j\), vanishes at \(x=0\) and satisfies
\[
 (\alpha_j)_x=h_j(\mu_j-k_jF_j).
\]
In particular the circle-wide choice of the tangential additive constant introduces no uncontrolled motion of the origin.

Write \(k,F,R\) also for the gauge pullbacks. The curvature equation takes the conservative form
\[
 \partial_t(hk)=-h^{-1}\partial_{xx}F+\partial_x(\alpha k),
 \qquad h^{-2}k_{xx}=F-k^3/2 .
                                                               \tag{4}
\]
At the chosen interior time the value of \(|k|\) at zero is bounded below uniformly and \(\|k_x\|_\infty\) is bounded by (3). Passing to one sign and a subsequence, a single nonnegative smooth test \(\phi\) supported in a sufficiently small interval about zero has \(\left|\int h_j k_j\phi\,dx\right|\ge b>0\) at \(t_j\).

## Compactness without a pointwise upper bound on the deficit

Fix any bounded \(x\)-interval \(I\) containing zero. Split
\[
 \alpha^{(0)}(t,x)=h(t)\int_0^x(\mu-\lambda k^2)\,dw,\qquad
 \alpha^{(1)}(t,x)=-h(t)\int_0^x kR\,dw.
\]
On \(I\) the first term is bounded in \(L_t^2L_x^\infty\), by (3) and the \(L_t^2\) bound on \(\mu\). For the second,
\[
 \|\alpha^{(1)}k\|_{L_t^1L_x^\infty(I)}
 \le C_I\|\|k\|_\infty^2\|_{L_t^2}\|R\|_{L^2_{t,x}(I)}\longrightarrow0.
\]
Also \(\|\alpha^{(0)} k\|_{L_t^{4/3}L_x^\infty(I)}\le C_I\), while \(F=\lambda k+R\) is bounded in \(L^2_{t,x}(I)\).

The bounds (3) place \(h_j k_j\) in a bounded set of \(L_t^2H_x^1(I)\). The conservative equation bounds their time derivatives in \(L_t^1H_x^{-2}\) on each smaller interval, for instance after a smooth cutoff. The compact inclusion \(H^1\hookrightarrow L^2\) on bounded intervals and the time-derivative compactness theorem thus give local strong \(L^2_{t,x}\) convergence, after extraction, to \(h_*K\). Equivalently, mollify in \(x\) using the \(L^2\) derivative bound and apply time compactness to the tested functions. For each fixed smooth compactly supported test the pairings with \(h_jk_j\) are even asymptotically equicontinuous on \([0,T]\): their derivatives are bounded by an \(L_t^2\) term plus an \(L_t^{4/3}\) term and an \(L_t^1\) error tending to zero. Consequently the nonzero pairing at the interior times \(t_j\) survives on a time interval of positive length. In particular \(K\) is nonzero. [Simon's time-derivative compactness theorem](https://www.karlin.mff.cuni.cz/~kaplicky/pages/pages/2012z/b2.pdf)

By interpolation, \(k_j\to K\) strongly in \(L^p_{t,x,\mathrm{loc}}\) for \(p<4\). The same uniform \(L_t^4L_x^\infty\) bound holds locally for \(K\) by Fatou and subsequence convergence on almost every slice. Hence \(\alpha_j^{(0)}\to\alpha_*=h_*\int_0^x(\mu_*-\lambda_*K^2)\,dw\) in \(L_t^{3/2}L_x^\infty(I)\), by the strong \(L^3_{t,x}\) convergence. Thus \(\alpha_j^{(0)}k_j\to\alpha_*K\) in \(L^1_{t,x}(I)\), while (2) gives \(F_j\to\lambda_*K\) strongly in local \(L^2\). Passing to the two distributional equations (4) gives, with \(\partial_s=h_*^{-1}\partial_x\),
\[
 K_{ss}=\lambda_*K-K^3/2,\qquad
 \partial_t(h_*K)=-h_*^{-1}(\lambda_*K)_{xx}+(\alpha_*K)_x .
                                                               \tag{5}
\]

## Regularity of the limiting patch and the contradiction

For almost every time the spatial equation is an ordinary differential equation with bounded solution on compact intervals, so \(K\) is spatially smooth there. On each interior compact interval the elementary local interpolation bound
\(\|K_s\|_\infty\le C_I(\|K\|_\infty+\sqrt{\|K\|_\infty\|K_{ss}\|_\infty})\) on a slightly larger interval gives \(\|K_s\|_\infty\in L_t^2\), since \(\|K_{ss}\|_\infty\le C(\|K\|_\infty+\|K\|_\infty^3)\). This interpolation follows by taking first differences with an increment bounded by the interval margin and optimizing the increment. From (5) it now follows that
\[
 \partial_tK=\alpha_*K_s-\lambda_*^2K-\lambda_*K^3/2 .
\]
The right side is in \(L_t^1 C_x(I)\). Integration in time gives a representative continuous in time with values in \(C(I)\). In particular \(K\) is bounded on compact spacetime subsets. The spatial equation, first differences and nested interior intervals now bound the spatial derivatives, and identify their continuous representatives in time: \(K_{ss}\) is continuous by its equation, and \(K_s\) is the uniform limit of first differences of \(K\). Repeated spatial differentiation of that equation gives the higher jets. The displayed time equation is smooth in those jets, \(\alpha_*\) and the smooth scalar functions \(h_*,\lambda_*\). These identities justify the commuting spatial and time differentiations below on any interior patch.

Set \(D_t=\partial_t-\alpha_*\partial_s\). The equations give \([D_t,\partial_s]=-\lambda_*K^2\partial_s\) and \(D_tK=-\lambda_*^2K-\lambda_*K^3/2\). Write \(\lambda=\lambda_*\) for brevity. Differentiating \(K_{ss}+K^3/2=\lambda K\), with this commutator, gives at \(K\ne0\)
\[
 \lambda'=-\lambda(5K_s^2+4\lambda K^2-K^4)
          =-\lambda(5C(t)+9\lambda K^2-\tfrac94K^4),
 \qquad K_s^2=C(t)+\lambda K^2-K^4/4.
\]
On each spatial component of the nonzero set the polynomial has fixed value, forcing \(K\) spatially constant. Around a nonzero spacetime point this implies \(K^2=2\lambda\), and the material equation forces \(\lambda'=-4\lambda^3\). The energy and length laws gave \(\lambda'=-6\lambda^3\) with \(\lambda>0\). This contradiction proves (1).

Formula (1) does not force \(U\) bounded. It quantifies the failure of the optimal scaled growth rate to persist on consecutive windows and leaves the regimes with larger \(B\) open. This macroscopic theorem is an analytic proof; the residual identity and geometric lower bounds that motivate the argument are separately Lean-verified.
