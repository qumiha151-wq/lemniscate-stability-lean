# A uniform loss from maximal product growth on every fixed RMS window

Let \(X\) solve the smooth closed planar free elastic flow, \(L=\int ds,\ E=\int k^2ds/2,\ U=EL\), and \(\rho=1/2-LU'/E^3\). For each \(T>0\) there exist \(c_T>0\) and \(u_T<\infty\) such that every starting slice with \(U_0\ge u_T\) satisfies
\[
           m_0^4\int_{t_0}^{t_0+T/m_0^4}\rho(t)\,dt\ge c_T,
                  \qquad m_0^2=2E(t_0)/L(t_0).                       \tag{1}
\]
The solution must exist through the window. Constants are independent of the immersion, rotation number and covering multiplicity. In the length-normalized clock \(\tau=\int L^{-4}dt\), there is a universal \(\kappa>0\) such that every global flow with finite terminal clock satisfies
\[
       \liminf_{\tau\to\tau_*} U(\tau)\sqrt{\tau_*-\tau}
                        \ \ge 1+\kappa.                               \tag{2}
\]
In particular, a single flow cannot have both \(L(t)\sim\ell t^{1/3}\) and \(E(t)\sim(\ell/\sqrt3)t^{-1/6}\), regardless of the relative error rates. Unrestricted fourth-root length growth remains open.

The logarithmic cost in the [first intermediate-scale proof](IntermediateCurvatureTubes.md) came from asking for small unweighted squared residual in every selected tube. The following argument uses a first-power tail and a scaled second power. The first-power costs sum over all dyadic amplitudes.

## Stopped sampling without a scale count

If (1) failed, dilating space by the initial \(m_0\) and time by \(m_0^4\) would give \(U_0\to\infty,\ \int_0^T\rho\,dt\to0\). In these units set \(P=L(0)=\sqrt{2U_0}\), \(\lambda=E/(2L)\), \(F=k_{ss}+k^3/2,\ R=F-\lambda k,\ W=(k^2/2-\lambda)T_{\rm tan}+k_sN\). Write \(\langle f\rangle=L^{-1}\int fds\), \(d=\int_0^T\langle R^2\rangle dt\). The physical identities give \(L(t)\asymp P\), uniform convergence \(\lambda(t)\to(16+12t)^{-1/2}\), \(\langle k^2\rangle=4\lambda,\ d\to0\). On \(I=[T/4,T/2]\), the [complete concentration theorem](CriticalCurvatureConcentration.md) supplies \(b_j\to\infty\) such that the spacetime energy \(\int_I\langle k^2{\bf1}_{|k|\ge b_j}\rangle dt\) stays bounded below. Split these starting pairs into dyadic bands \(H=2^n,\ n\ge0,\ H^2\le|W|<4H^2\). They cover the retained energy for all sufficiently large \(j\); \(H\to\infty\) uniformly over these retained starts, and \(k^2\le CH^2\) within each band. No upper bound on the number of bands is needed.

Sample starting times \(t\in I\) and material labels \(q\) by \(dt\,ds(t)/L(t)\). Put \(h=\min(1,T/4)>0\), \(v=t+\theta/H^2\) for \(0\le\theta\le h\), and stop at the first \(\theta\) where \(g(v,q)=ds(v)/ds(t)\) reaches \(1/2\), or at \(h\) if this never happens. All following integrals stop at that time, denoted by \(\sigma\). Write \(x=H s\) where \(s\) is current signed arclength from the material origin \(q\), \(r=R/H\) and \(\epsilon=H^{-2}\). The central value \(r_0(\theta)=R(v,q)/H\) is evaluated on the moving material label.

For \(p=1,2\) put
\[
 T_p=\int_0^\sigma\!\!\int_{-4}^4 |r|^pdx\,d\theta,\qquad
 C_p=\int_0^\sigma |r_0|^p d\theta,\qquad
 J_0=H^{-5}\int_{|s|\le4/H}R(t)^2ds .
\]
At any \(t,v\), starting labels still alive satisfy \(ds(t)\le2ds(v)\) on that set. Spatial Fubini on the slice at \(v\) gains a factor \(8/H\) for a tube observable. Time Fubini gains at most \(h/H^2\) from the possible starting times. For the central observable there is no spatial averaging, but its conversion from \((x,\theta,r)\) to physical variables has one fewer factor of \(H\). Consequently, for either \(T_1\) or \(C_1\), restricted to contributions from points where \(|R|>\delta H\), its unweighted integral over all starting pairs is bounded by
\[
           C H^{-1}\int_0^T\langle |R|{\bf1}_{|R|>\delta H}\rangle\,dv.
\]
For example the tube conversion factor for \(T_1\) is \(H^2\), yielding \(C H^2 H^{-1} H^{-2}=C/H\); the conversion for \(C_1\) is \(H\), yielding \(CH H^{-2}=C/H\). Uniform bounds on \(L(v)/L(t)\) suffice here. The unweighted starting-pair integrals of \(\epsilon T_2,\epsilon C_2\) are at most \(CH^{-4}d\), and that of \(J_0\) is at most \(CH^{-6}d\).

Restrict now to the retained band and weight starting pairs by their \(k^2\). For the first-power tails, multiply by \(CH^2\), then sum over all bands. The pointwise geometric sum \(\sum_{H<|R|/\delta}H\le 2|R|/\delta\) gives a total at most \(Cd/\delta\). The portions \(|R|\le\delta H\) of \(T_1+C_1\) are at most \(C\delta\) at every start, and total starting energy is bounded. The summed energy-weighted costs of \(\epsilon(T_2+C_2)\) and \(J_0\) are bounded by \(Cd\sum_H(H^{-2}+H^{-4})\le C'd\). Choose \(\delta_j\downarrow0\) with \(d_j/\delta_j\to0\). From the positive retained energy, there is then a sequence of starts on which
\[
             T_1+C_1+\epsilon(T_2+C_2)+J_0\longrightarrow0 .          \tag{3}
\]
This selection deliberately includes starts whose density might reach \(1/2\). The following estimates prove that these selected starts survive throughout the window.

## The local estimate with weak forcing

Write \(K=k/H,\ f=F/H=\lambda K+r\). In the moving arclength gauge the known equations give \(K_{xx}+K^3/2=\epsilon f\), \(\alpha_x=-Kf,\ \alpha(0)=0\). For \(V=(K^2/2-\epsilon\lambda)T_{\rm tan}+K_xN\), one has \(V_x=\epsilon rN\). At the initial point \(|V|\in[1,4]\) and its initial oscillation across the window is \(o(1)\) by \(J_0\to0\). Thus \(\int_{-3}^3K(0,x)^2dx\le C_0\), and after extraction the initial curvatures converge locally in \(C^1\) to a nonzero rectangular oscillator as in the preceding proof. In fact \(\|\epsilon r(0,\cdot)\|_2^2=J_0\), and the initial oscillator first integral at zero is at least one. A fixed smooth spatial test supported in \((-1,1)\) has nonzero pairing with this limit.

Put \(u(\theta)=\int_{-4}^4 |r(\theta,x)|dx\). From (3), \(\int u=o(1)\), \(\epsilon\int u^2\le8\epsilon T_2=o(1)\). As before choose \(\chi=\psi(|x|+b(\theta))\) with \(\psi=1\) on \([0,2]\), \(\psi=0\) on \([3,\infty)\), \(\psi'\le0\); put \(m=\int\chi K^2/2\). While \(b\le1\) the weighted virial identity with any smooth nonnegative unit-mass test \(\phi\) supported in \((-1,1)\) gives, with \(Y=\sup_{[-4,4]}|V|\),
\[
   (Y-\epsilon u)_+^2
       \le C[1+(1+Y)m+\epsilon\sqrt{1+Y}\,u].
\]
Here \(\int\phi\epsilon Kr\) was bounded by the supremum of \(|K|\) times \(\epsilon u\), and \(\sup K^2\le2(Y+\epsilon\lambda)\). If \(Y\le2\epsilon u\) there is nothing to prove; otherwise the final term is at most \(C Y\sqrt{1+Y}\), which is absorbed by \(Y^2\) for sufficiently large \(Y\). Young's inequality then gives
\[
                 Y\le C(1+m+\epsilon u).                              \tag{4}
\]
Choose \(M>C_0+2\) fixed. While \(m\le M\), the one-sided tangential speed satisfies \({\rm sgn}(x)\alpha(x)\le\int_{-4}^4 |Kr|dx\le C_M(1+\sqrt{\epsilon u})u\), using the positive term \(\lambda K^2\) in \(Kf\). Set \(b(0)=0,\ b'=C_M(1+\sqrt{\epsilon u})u\) with this constant. Its time integral on the entire stopped window is \(o(1)\), since \(\sqrt{\epsilon}\int u^{3/2}\le(\int u)^{1/2}(\epsilon\int u^2)^{1/2}\). Thus the cutoff has the required plateau, and \(\chi_\theta-\alpha\chi_x\le0\) through the \(m\) bootstrap.

The exact energy density equation has sink \(-\epsilon f^2\) and flux \(K_x r-Kr_x+\alpha K^2/2\). Testing and integrating by parts as in the [local energy argument](CriticalCurvatureConcentration.md) gives
\[
 m'\le C[(1+m)u+\epsilon u^2].
\]
The integrated right side while \(m\le M\) tends to zero, so \(m\) never reaches \(M\). At the central material label,
\[
 -\log g(v,q)\le \int_0^\theta |K(w,0)r_0(w)|dw
       \le C_M C_1+C(\int u)^{1/2}(\epsilon C_2)^{1/2}=o(1).
\]
Here \((\log g)_\theta=Kf\) and (4) bounds \(K^2\) by \(C_M+C\epsilon u\). This proves \(\sigma=h\) for all sufficiently large indices.

## The limiting contradiction

By (4), \(\int_0^h(\sup K^4+\sup K_x^2)d\theta\le C(h+\epsilon^2\int u^2)=O(1)\). The already obtained \(m\) bound controls \(\int K^2 dx\) uniformly at each time on any interval strictly inside \([-1,1]\). In such a window the conservative equation is \(K_\theta=-f_{xx}+(\alpha K)_x\). The part \(-\int_0^x\lambda K^2dy\) of \(\alpha\) is uniformly bounded. The remaining flux is estimated directly:
\[
 \int_0^h\sup_{|x|<1}\left|K(x)\int_0^x K r\,dy\right|d\theta
                  \le C\int_0^h(1+\epsilon u)u\,d\theta=o(1).
\]
Also \(f=\lambda K+r\) with \(r\to0\) in local \(L^1\). After cutting off inside the window, \(K\) is bounded in \(L^2_\theta H^1_x\) and its time derivative in \(L^1_\theta H^{-3}_x\); in one dimension \(H^3\) controls the supremum of the second derivative of a test. Time-derivative compactness gives strong local \(L^2\) convergence, and interpolation gives strong convergence in every \(L^p,\ p<4\). The initial nonzero pairing survives on a fixed interior time interval: its change on an interval of length \(\Delta\theta\) is \(O(\Delta\theta)+o(1)\) by the uniform local mass bound, the bounded part of \(\alpha\), and the two vanishing \(L^1\) errors above. For the limiting nonlinear flux, \(\int_0^x\lambda K^2dy\) converges strongly in \(L^{3/2}_\theta L^\infty_x\) by strong \(L^3\), which suffices after multiplication by \(K\).

After extraction of the initial times the coefficient \(\lambda\) converges uniformly on the full small window to a positive constant \(\lambda_c\). The two limiting equations and their smooth local representative are the ones in the [intermediate-scale compatibility proof](IntermediateCurvatureTubes.md):
\[
 K_{xx}=-K^3/2,\quad D_\theta K=-\lambda_c K^3/2,\quad
 [D_\theta,\partial_x]=-\lambda_c K^2\partial_x.
\]
They imply \(K(K^4-5K_x^2)=0\), which is incompatible with the spatial first integral on a nonzero patch. This proves (1).

## Consequences on both clocks

For (2), suppose there were a sequence of finite-clock flows and times with \(\delta=\tau_*-\tau\to0\) and \(U\sqrt\delta\to1\). The finite-clock identity gives \(A=\delta-U^{-2}=2\int_\tau^{\tau_*}\rho\,d\sigma=o(\delta)\). On \([\tau,\tau+\delta/2]\), therefore, \(U\asymp\delta^{-1/2}\) with absolute comparison constants. The moving RMS measure \(d\theta=4U^2d\tau\) assigns a duration bounded above and below to this interval, and \(\int\rho\,d\theta=o(1)\). The scalar estimate \(|(\log\lambda)_\theta|\le C(1+\sqrt\rho+\rho)\) controls the comparison to the initial RMS scale in both directions by absolute constants. This gives a fixed positive initial RMS duration with vanishing integrated loss, contradicting (1) since \(U\to\infty\). This contradiction for arbitrary sequences proves a universal strict gap in (2). [Finite-clock identity and comparison](FiniteClockGrowthCorrection.md)

For each fixed \(0<a<1\) there is likewise \(\kappa_a>0\) such that at every sufficiently high \(U(\tau)=H\),
\[
                U(\tau+a/H^2)\le
                     \big((1-a)^{-1/2}-\kappa_a\big)H                \tag{5}
\]
on any global flow with finite or infinite terminal clock. The endpoint exists by \(H^{-2}\le\tau_*-\tau\) in the finite case. If the relative gap in (5) vanished along a sequence, then \((U^{-2})_\tau=-1+2\rho\) gives \(\int\rho\,d\tau=o(H^{-2})\) on this interval. It also gives \(U\asymp_a H\) on each prefix, and the same clock comparison contradicts (1).

If \(L(t)\sim\ell t^p\) with \(1/4<p<1/2\), its remaining clock is \(\delta(t)\sim\ell^{-4}t^{1-4p}/(4p-1)\). Equations (2) and the scalar physical energy comparison imply, without any energy asymptotic assumption,
\[
 \liminf_{t\to\infty} t^{1/2-p}E(t)
 \ \ge\ \ell\max\!\left\{\frac{p}{\sqrt{1-2p}},\ (1+\kappa)\sqrt{4p-1}\right\}.
\]
The improved coefficient applies throughout a neighborhood of \(p=1/3\); at \(p=1/3\) it exceeds \(\ell/\sqrt3\) by a universal factor. This does not exclude \(L(t)\asymp t^{1/3}\) alone. The [physical energy comparison](PhysicalPowerDeficit.md) proves the first entry by time-secant inequalities.

This proof, the uniform positive constants, and the physical-clock consequences are written arguments. None of the new assertions in this manuscript has been formalized in Lean.
