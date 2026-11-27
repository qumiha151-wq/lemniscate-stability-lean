# The averaged loss from maximal growth is at least logarithmic at high product

Write \(U=EL,\ \eta=LU'/E^3,\ \rho=1/2-\eta\) on a smooth closed planar free elastic flow. For every fixed \(T>0\) there are constants \(c_T>0\) and \(u_T<\infty\) such that every positive-time slice with \(U_0=U(t_0)\ge u_T\) satisfies
\[
 m_0^4\int_{t_0}^{t_0+T/m_0^4}\rho(t)\,dt
       \ \ge\ \frac{c_T}{\log(2+U_0)},\qquad m_0^2=2E(t_0)/L(t_0).
                                                                      \tag{1}
\]
Constants are independent of the initial shape, multiplicity and turning number. The flow is assumed to exist through the displayed interval. The argument combines a time-and-label counting estimate within each curvature scale and an incompatibility at the intermediate time scale \(H^{-2}\). The number of relevant scales gives the logarithm. The result permits an average loss tending to zero.

## Preliminary bounds and choice of amplitude bands

Suppose (1) fails. Shift physical time to the chosen initial slices and apply the fixed dilation \(m_0\) of space, \(m_0^4\) of time. There would then be a sequence with \(U_0\to\infty\) and \(\log(2+U_0)\int_0^T\rho\,dt\to0\). The newly normalized length \(P=L(0)=\sqrt{2U_0}\) tends to infinity. Put \(F=k_{ss}+k^3/2,\ \lambda=E/(2L),\ R=F-\lambda k,\ W=(k^2/2-\lambda)T_{\rm tan}+k_sN\), where \(T_{\rm tan}\) denotes the unit tangent. Angle brackets denote the arclength mean on each slice. Write
\[
    d=\int_0^T\langle R^2\rangle dt .
\]
The scalar equations give \(\lambda\to(16+12t)^{-1/2}\) uniformly, \(L(t)\asymp P\) uniformly, \(\langle k^2\rangle=4\lambda\), and \(\langle R^2\rangle=8\lambda^3\rho\). Thus \(d\log P\to0\). On the fixed starting-time interval \(I=[T/4,T/2]\), discard times with \(\langle R^2\rangle>1\). These remove at most \(O(d)\) of \(\int_I\langle k^2\rangle dt\). On the remaining times \(D=\int F^2ds=O(P)\), \(E=O(P)\), hence \(\sup|k|\le C P^{1/3}\) by the geometric stress inequality. Also
\[
 \langle |W|^2\rangle=\tfrac34\langle k^4\rangle-2\lambda\langle k^2\rangle
                      +\lambda^2-\langle kR\rangle\le C(1+P^{2/3}).
\]
Since \(W_s=RN\), its oscillation is at most \(L\langle R^2\rangle^{1/2}\le CP\). Its supremum on such slices is therefore at most \(CP\). [Physical geometric stress bound](../../LengthGrowth/ActualFlow/ArclengthCoercivity.lean)

By the [concentration theorem](CriticalCurvatureConcentration.md), on \(I\) the part of \(\int_I\langle k^2\rangle dt\) with \(|k|\) bounded tends to zero. By diagonalization select thresholds \(b_j\to\infty\) so the energy from \(|k|\ge b_j\) and from the retained times is bounded below by a positive constant. At these labels \(|W|\ge k^2/2-\lambda\) tends uniformly to infinity. Separate them by dyadic \(H=2^\ell\ge1\) into disjoint bands \(H^2\le |W|<4H^2\). There are at most \(C\log P\) nonempty retained bands. In each \(k^2\le CH^2\).

## Counting prospective moving material tubes in each band

Fix \(h=\min(1,T/4)>0\). For each \(t\in I\) and each material origin \(q\), consider its forward window \(t\le v\le t+h/H^2\). The spatial arcs \(B_v(q)\) have current signed arclength radius \(4/H\) about that moving material point. The length \(L\asymp P\) ensures these are ordinary local charts for large \(j\). The sampling measure on starting pairs is \(dt\,ds(t)/L(t)\), with no weight by curvature. Define
\[
 J_0=H^{-5}\int_{B_t(q)}R(t)^2ds,\qquad
 J=H\int_t^{t+h/H^2}\int_{B_v(q)}R(v)^2ds\,dv .
\]
Call the start noncollapsing if the local density \(g(v,q)=ds(v)/ds(t)\) at this material label never falls below \(1/2\) within that window. From \(g_v=kFg\ge-R^2g/(4\lambda)\), the fraction of collapsing starts at time \(t\) is at most \(C\int_t^{t+h/H^2}\langle R^2\rangle dv\), using uniform length comparison. Its time integral is at most \(C H^{-2}d\).

For each \(t,v\), arclength at \(t\) restricted to the noncollapsing starts is dominated by \(2\,ds(v)\). Fubini on the periodic slice at \(v\) bounds the mean over such starts of \(\int_{B_v(q)}R^2ds\) by \(C H^{-1}\langle R(v)^2\rangle\), with the mean still normalized by the full \(L(t)\). Therefore the integral of \(J\) over noncollapsing starting pairs is at most \(C H^{-2}d\), and the integral of \(J_0\) over all starting pairs is at most \(C H^{-6}d\). For any \(0<z<1\), collapsing starts together with starts where \(J>z\) or \(J_0>z\) have sampling measure \(\le C H^{-2}d/z\). This assertion also bounds the integral over the intersection with the retained band after multiplying by \(k^2\le CH^2\): the lost curvature energy on that band is at most \(Cd/z\).

Summing the last bound over all retained bands costs at most \(C d\log P/z\). Take a positive \(z_j\to0\) with \(d_j\log P_j/z_j\to0\), for example \(z_j=(d_j\log P_j)^{1/2}+j^{-1}\). A starting pair remains on account of the positive retained energy. It has \(J,J_0\to0\) and belongs to a band \(H_j\to\infty\) because \(|k|\ge b_j\). Take a subsequence of starting times converging to an interior \(t_*\).

## Intermediate curvature evolution

At these starts use \(x=H_js\) for current arclength from the chosen material point, \(\theta=H_j^2(v-t)\) for time, \(K=k/H_j,\ r=R/H_j,\ \epsilon=H_j^{-2},\ f=F/H_j=\lambda K+r\). The spatially scaled actual curve has velocity \(-fN\) at fixed material labels in this time variable. On \(|x|\le4,\ 0\le\theta\le h\), the genuine equations are
\[
 K_{xx}+K^3/2=\epsilon f,\qquad
 \alpha_x=-Kf,\quad\alpha(0)=0,\qquad
 K_\theta=-f_{xx}-K^2 f+\alpha K_x .
\]
Here \(\alpha\) is the tangential velocity in the current arclength gauge. Equivalently \(K_\theta=-f_{xx}+(\alpha K)_x\). The integral of \(r^2\) on this spacetime rectangle is \(J\to0\). At its initial time the squared spatial \(L^2\) norm of \(\epsilon r\) is \(J_0\to0\). The rescaled stress \(V=(K^2/2-\epsilon\lambda)T_{\rm tan}+K_xN\) has initial norm between 1 and 4 at the origin, and \(V_x=\epsilon rN\). Hence its initial oscillation on \([-4,4]\) tends to zero. At the initial time \(K,K_x\) are bounded and \(K_{xx}=-K^3/2+\epsilon\lambda K+\epsilon r\). Integrating this last equation gives initial local \(C^1\) subsequential convergence to a solution of the zero-force oscillator equation. Its initial first integral \(K_x^2+K^4/4\) is at least one at the origin. In particular one fixed smooth spatial test supported in \((-1,1)\) has a nonzero pairing with this initial limit, including when the chosen origin itself is a zero of curvature.

The moving-cutoff estimate of the [concentration theorem](CriticalCurvatureConcentration.md) applies uniformly in this intermediate scaling. For precision, the rescaled energy density \(e=K^2/2\) satisfies
\[
   e_\theta=-\epsilon f^2+
       \partial_x(K_x r-Kr_x+\alpha e).
\]
For the shrinking cutoff use \(b'=\|r(\theta)\|_{L^2(-4,4)}^2/(4\lambda)\), since \(Kf\ge-r^2/(4\lambda)\) with \(\lambda\) bounded away from zero. For the spatial stress estimate use \(V_x=\epsilon rN\) and the oscillator parameters \(\epsilon\lambda,\epsilon r\) in the weighted spatial identity. It requires an upper bound for \(\epsilon\lambda\) and uses no reciprocal of it. Consequently \(m=\int\chi e\) obeys \(m'\le C[(1+m)\|r\|_2+\|r\|_2^2]\) and is bounded. In particular \(\int_0^h(\sup_{|x|\le3}K^4+\sup_{|x|\le3}K_x^2)d\theta\le C\), uniformly as \(\epsilon\to0\).

On this window \(\lambda\to\lambda_*(t_*)>0\) uniformly. Denote this constant by \(\lambda_c\). The local compactness argument from the [fourth-moment proof](CriticalFourthMoment.md) applies with \(h_{\rm metric}=1,\ \mu=0\): \(K\) converges strongly locally in every \(L^p,\ p<4\); the initial nonzero tested curvature persists over a fixed initial interior time interval. Indeed \(f\) is bounded in \(L^2\), and splitting \(\alpha=-\int_0^x(\lambda K^2+Kr)dy\) bounds the first part in \(L^2_\theta L_x^\infty\) and makes the second \(o(1)\) in \(L^{4/3}_\theta L_x^\infty\). Passing to the two limiting equations yields
\[
 K_{xx}=-K^3/2,\qquad
 D_\theta K=-\lambda_c K^3/2,\qquad
 D_\theta=\partial_\theta-\alpha\partial_x,\quad
 \alpha_x=-\lambda_c K^2 .
\]
The limit is smooth on a smaller interior rectangle, by the same local argument from the spatial first integral and the evolution equation as in the fourth-moment proof. In particular \([D_\theta,\partial_x]=-\lambda_c K^2\partial_x\). Apply \(D_\theta\) to \(K_{xx}+K^3/2=0\) and use the two displayed equations. The result is
\[
                  0=\lambda_c K(K^4-5K_x^2) .
\]
On a spatial interval with \(K\ne0\), the first integral \(K_x^2+K^4/4=C(\theta)\) then forces \(K^4=20C(\theta)/9\), so \(K\) is spatially constant. The spatial equation excludes a nonzero constant. This contradicts the surviving nonzero test pairing and proves (1).

## Consequences for the length-normalized clock

Let \(\tau(t)=\int_0^t L^{-4}dr\), and if \(\tau_*=\tau(\infty)<\infty\) put \(\delta=\tau_*-\tau\). For every such individual flow and all sufficiently late times,
\[
               U(\tau)-\delta^{-1/2}
                  \ \ge\ c\,\frac{\delta^{-1/2}}{\log(1/\delta)}.       \tag{2}
\]
Indeed \(A=\delta-U^{-2}=2\int_\tau^{\tau_*}\rho\,d\sigma\ge0\). Suppose along a sequence \(A\log(1/\delta)/\delta\to0\). On the half-window \([\tau,\tau+\delta/2]\) we have \(U\asymp\delta^{-1/2}\), and the moving RMS time \(d\theta=4U^2d\tau\) has duration bounded above and away from zero. Moreover \(\int\rho\,d\theta\le C A/\delta=o(1/\log U(\tau))\). The exact inequality \(|(\log\lambda)_\theta|\le C(1+\sqrt\rho+\rho)\) bounds the ratio of the initial and moving RMS scales throughout this interval. Thus it contains a fixed positive initial RMS duration with integrated loss \(o(1/\log U(\tau))\), contradicting (1). Hence \(\liminf A\log(1/\delta)/\delta>0\). The inequality \(A\le2\delta^{3/2}(U-\delta^{-1/2})\) proves (2). [Physical-to-normalized clock comparison](FiniteClockGrowthCorrection.md)

Likewise for any fixed \(0<a<1\) and any sequence of starts \(H=U(\tau)\to\infty\), on a finite or infinite terminal clock,
\[
        \liminf \frac{\log H}{H}
             \left[\frac{H}{\sqrt{1-a}}-U(\tau+a/H^2)\right]>0 .       \tag{3}
\]
If the expression tended to zero along a subsequence, integration of \((U^{-2})_\tau=-1+2\rho\) would give \(\int_\tau^{\tau+a/H^2}\rho\,d\sigma=o(H^{-2}/\log H)\). On all prefixes it would follow that \(U\asymp_a H\). The same comparison gives a fixed initial RMS window with integrated loss \(o(1/\log H)\), again contradicting (1). The endpoint exists by \(H^{-2}\le\tau_*-\tau\) when the terminal clock is finite.

In particular, if \(L(t)\asymp t^{1/3}\) alone, then \(\delta(t)\asymp t^{-1/3}\) and (2) gives \(U(t)-\delta(t)^{-1/2}\gtrsim t^{1/6}/\log t\), uniformly for large \(t\). Thus matched laws \(L(t)=\ell t^{1/3}(1+o(1/\log t))\), \(E(t)=(\ell/\sqrt3)t^{-1/6}(1+o(1/\log t))\) are impossible. The two leading equivalences with unspecified remainders and unrestricted fourth-root growth remain open. The band selection, intermediate dynamics and asymptotic bounds in this note are written proofs, without Lean verification.
