# A strict physical energy gap at every super-fourth-root power law

For each \(1/4<p<1/2\) there exists \(\varepsilon_p>0\), independent of the flow and of \(\ell>0\), such that every smooth global closed planar free elastic flow with \(L(t)\sim\ell t^p\) satisfies
\[
        \liminf_{t\to\infty}\frac{t^{1/2-p}E(t)}{\ell}
                  \ \ge\ \frac{p}{\sqrt{1-2p}}+\varepsilon_p .         \tag{1}
\]
The coefficient \(p/\sqrt{1-2p}\) is sharp for the scalar inequalities \(E'=-D,\ (L')^2\le2ED\): the exact scalar profiles \(L=\ell t^p,\ E=\ell p(1-2p)^{-1/2}t^{p-1/2},\ D=-E'\) attain it. For actual curves (1) holds even when the normalized energy has no limit. The existence of any actual curve with this length law for \(p>1/4\) remains open.

## A necessary evolution law for curvature-proportional speed

Consider a sequence of smooth closed flows on a time interval \([a,b]\) of positive length, in one fixed parabolic normalization per flow. Suppose \(L_j(t)\asymp P_j\to\infty\) uniformly there, \(0<c\le\langle k_j^2\rangle\le C\), and \(v\) is a positive \(C^1\) function on the interval. Here \(\langle f\rangle=L^{-1}\int fds\). Then
\[
 \int_a^b\langle(F_j-v(t)k_j)^2\rangle dt\longrightarrow0
                \quad\Longrightarrow\quad v'=-4v^3\text{ on }[a,b].
                                                                      \tag{2}
\]
This condition on the coefficient refers to normalized physical time; no individual \(F_j\) is assumed to equal \(v k_j\).

To prove it write \(R_j=F_j-vk_j\). First, on every compact interior time interval \(I\), the squared curvature is uniformly integrable in amplitude in the limiting sequence:
\[
 \lim_{B\to\infty}\limsup_{j\to\infty}
            \int_I \langle k_j^2{\bf1}_{|k_j|>B}\rangle dt=0.          \tag{3}
\]
Indeed if a subsequence carries positive energy at \(|k_j|>B_j\to\infty\), it already supplies the high-amplitude starting pairs for the [weak-residual tube argument](UniformMacroscopicDeficit.md). For clarity, use \(W=(k^2/2-v)T+k_sN\) and split into \(|W|\in[H^2,4H^2)\). The counting of first-power residual tails, the bounds for \(\epsilon\int r^2,\epsilon\int r_0^2\), the initial \(H^{-5}\int R^2\) test, and the first stopping time of the material density are identical, using \(L(t)\asymp P_j\), the bound on total starting energy and \(\int\langle R^2\rangle\to0\). The upper and lower bounds on \(v\) give precisely the constants needed for the shrinking cutoff and the estimate \(\alpha_x=-K(vK+r)\). On the selected \(H^{-2}\) time intervals the coefficient converges uniformly to a positive constant \(v_c\) by continuity. The resulting nonzero patch would satisfy
\[
 K_{xx}=-K^3/2,\qquad D_\theta K=-v_cK^3/2,\qquad
             [D_\theta,\partial_x]=-v_cK^2\partial_x .
\]
This is impossible by the intermediate compatibility identity \(K(K^4-5K_x^2)=0\). This proves (3) without first imposing any ODE on \(v\).

Suppose now \(v'+4v^3\ne0\) at some interior time. By continuity choose a closed subinterval on which this difference never vanishes, leaving an interior interval of starting times and a fixed positive forward duration inside it. The lower bound on mean curvature squared together with (3) shows that \(|k_j|\ge a_0>0\) occupies a fixed positive fraction in spacetime on these starting times. Indeed the contribution from \(|k|<a_0\) can be made small, and the contribution from \(|k|>B\) small for some fixed \(B\), while the intermediate part is pointwise bounded by \(B^2\). Thus there are sets of times of measure bounded away from zero where at least a fixed arclength fraction has \(|k_j|\ge a_0\). Choose one of these times with \(\langle R_j^2\rangle=o(1)\). As in the [localized concentration argument](CriticalCurvatureConcentration.md), one can select a material point in this fraction with bounded initial local bending mass, bounded initial local squared residual and vanishing local spacetime squared residual. In detail, labels whose density ever falls below \(1/2\) during the chosen forward window have initial fraction \(o(1)\), since \(kF\ge-R^2/(4v)\); the rest of the initial measure is transported below twice running arclength. Fubini and Markov's inequality give the simultaneous local bounds.

In the current arclength chart from that material point, apply the moving-cutoff energy estimate with coefficient \(v\) to get bounded initial slope, bounded local spacetime \(\int(k^4+k_s^2)\), and nonzero initial tested curvature. The hypotheses in that estimate are just \(0<c\le v\le C\) and the selected initial and local spacetime bounds. The conservative curvature equation in this gauge is \(k_t=-F_{ss}+(\alpha k)_s,\ \alpha_s=-kF,\ \alpha(0)=0\); it avoids any requirement on \(L'/L\). The same local compactness proof produces a nonzero interior patch with equations \(K_{ss}=v K-K^3/2,\ D_tK=-v^2K-vK^3/2,\ [D_t,\partial_s]=-vK^2\partial_s\). The regularity from the spatial first integral suffices to differentiate these equations once in time and twice in space when \(v\in C^1\). Their [compatibility identity](MacroscopicSaturation.md) gives on a nonzero open patch
\[
 v'=-v\big[5C(t)+9vK^2-\tfrac94K^4\big],
       \qquad C(t)=K_s^2-vK^2+K^4/4 .
\]
Here \(C(t)\) is spatially constant. Therefore \(K\) is spatially constant locally, its spatial equation gives \(K^2=2v\), and its material equation gives \(v'=-4v^3\). This contradicts the choice of subinterval. Since any nonzero interior value of \(v'+4v^3\) is excluded, continuity to the endpoints proves (2).

## Near attainment of the scalar coefficient forces proportional speed

Write \(e_p=p/\sqrt{1-2p}\). The physical identity \(-(E^2)'\ge (L')^2\) and finite partitions of \([t,bt]\), followed by \(b\to\infty\), give the scalar lower bound \(\liminf t^{1/2-p}E(t)/\ell\ge e_p\). [Physical energy comparison](PhysicalPowerDeficit.md)

If there were no uniform improvement in (1), choose a sequence of flows and initial times \(t_j\to\infty\) such that
\[
 P_j=\ell_jt_j^{p-1/4}\to\infty,\qquad
 \sup_{s\ge1}\left|\frac{L_j(t_js)}{\ell_j(t_js)^p}-1\right|\to0,\qquad
 \frac{t_j^{1/2-p}E_j(t_j)}{\ell_j}\to e_p .
\]
Each \(t_j\) can be taken arbitrarily late in its flow because the energy assertion is a liminf, the length equivalence holds on its entire tail, and \(p>1/4\).

Set \(X_j(s)=L_j(t_js)/(\ell_j t_j^p)\) and \(Y_j(s)=t_j^{1/2-p}E_j(t_js)/\ell_j\). Then \(X_j\to s^p\) locally uniformly on \([1,\infty)\) and \(\int_1^\infty |X_j'|^2ds\le Y_j(1)^2\to e_p^2\). By weak compactness and the distributional derivative, \(X_j'\rightharpoonup p s^{p-1}\) in \(L^2(1,\infty)\). The squared norm of this limit is exactly \(e_p^2\); hence convergence is strong. Furthermore,
\[
 0\le Y_j(s)^2-\int_s^\infty |X_j'|^2dr
     \le Y_j(1)^2-\int_1^\infty |X_j'|^2dr\longrightarrow0
\]
uniformly in \(s\ge1\), by the same monotone energy inequality. Thus \(Y_j(s)\to e_p s^{p-1/2}\) locally uniformly. The nonnegative measure with density \(-(Y_j^2)'-|X_j'|^2\) has total mass tending to zero.

Now dilate the actual curves by \(t_j^{-1/4}\) so their time is \(s=t/t_j\). Their true lengths and energies are respectively \(P_j X_j\) and \(P_jY_j\). On \([1,2]\) define \(v_j=X_j'/(2Y_j)\). This is the spatial least-squares coefficient \(\langle kF\rangle/\langle k^2\rangle\) of the dilated true flow. The energy and length identities give exactly
\[
        -(Y_j^2)'-|X_j'|^2
                   =2Y_j X_j\,\langle(F-v_j k)^2\rangle .
\]
The right side therefore has vanishing integral. The local uniform bounds on \(Y_j,X_j\) give
\[
       v_j\longrightarrow v(s)=\frac{\sqrt{1-2p}}{2\sqrt{s}}
                     \quad\text{in }L^2(1,2),\qquad
       \langle k^2\rangle=2Y_j/X_j\asymp1 .
\]
Consequently \(\int_1^2\langle(F-v(s)k)^2\rangle ds\to0\). All hypotheses of (2) hold. But \(v'/v^3=-2/(1-2p)\), which equals \(-4\) only at \(p=1/4\). This contradiction proves (1).

These are written proofs. The physical energy and length variations, including their connection to the position-defined free elastic equation, have separate Lean verification. The limiting coefficient rigidity (2) and the physical coefficient gap (1) have not been checked in Lean.
