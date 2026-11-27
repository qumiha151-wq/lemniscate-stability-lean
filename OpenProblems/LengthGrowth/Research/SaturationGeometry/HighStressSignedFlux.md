# Vanishing total signed length flux from high elastic stresses

Let smooth closed planar free elastic flows be given on one fixed time slab \([0,T]\), each in one fixed parabolic normalization, with \(L_j(t)\asymp P_j>0\) uniformly. Suppose \(\sup_{j,t}\langle k_j^2\rangle\le C\) and \(\sup_j\int_0^T\langle F_j^2\rangle dt\le C\), where \(F=k_{ss}+k^3/2\) and \(\langle\cdot\rangle=L^{-1}\int\cdot\,ds\). Write \(S=(k^2/2)T_{\rm tan}+k_sN\). Take any nondecreasing smooth \(\zeta\) on \([0,\infty)\) equal to zero on \([0,1]\) and one on \([4,\infty)\). For every \(B_j\to\infty\) and \(w\in C_c^1(0,T)\),
\[
     \frac1{P_j}\int_0^T w(v)\int \zeta(|S_j|/B_j^2)\, k_jF_j\,ds\,dv
                         \longrightarrow0 .                            \tag{1}
\]
This is a statement about the total signed physical length variation in those stress ranges. The integrand need not be small in absolute value. In particular, if on a compact interior time interval \(I\) the normalized curvature-square contribution from every bounded stress range tends to zero, then \((L_j(\sup I)-L_j(\inf I))/P_j\to0\). In fact bounded stress implies bounded curvature, and the same conclusion holds if the bending energy escapes every bounded curvature range there. These conclusions do not constrain the sign of the length flux from finite-amplitude profiles in a general flow.

## Sampling and chart properties

Put \(\psi(y)=\zeta(y)-\zeta(y/4)\), supported in \([1,16]\). Then \(\zeta(|S|/B_j^2)=\sum_{H}\psi(|S|/H^2)\) for \(H=B_j2^n,\ n\ge0\). The sum telescopes. Use a fixed compact time interval \(J\Subset(0,T)\) whose interior contains the support of \(w\) with a positive margin. For the broad starting ranges \(|S|/H^2\in[1/2,32]\), take measure \(H^2 ds(t)dt/P_j\) on \(J\), summed over \(H\). Its total is bounded uniformly. Indeed \(\sum H^2{\bf1}_{[1/2,32]}(|S|/H^2)\le C|S|\). With \(V=(1+|S|^2)^{1/2}\), one has \(|V_s|\le|F|,\ k^2\le2V,\ |k_s|\le V\). Integrating \((k k_s)'/V\) on the periodic slice and using \((kk_s)'=k_s^2+kF-k^4/2\) gives \(\int k_s^2/V\le C\int(k^2+|F|)ds\). Decomposing \(V=(1+k^4/4+k_s^2)/V\) gives the desired integral bound by the hypotheses. It also holds for the narrower range \(|S|/H^2\in[1,16]\).

The estimates in the [actual forced tube construction](PhysicalForcedRectangularTube.md) apply on either range with the present starting measure. The original energy-weighted proof uses the upper bound \(CH^2\) on the starting weight and a bound on its total mass, which we have just verified. Use both forward and backward charts. In the latter \(\theta=H^2(t-v)\) increases toward the past from a starting time \(t\); changing signs of the normal and tangential velocities gives the same limiting equations. The spatial force then equals the negative of \(\epsilon\) times the signed normal force, where \(\epsilon=H^{-2}\). Its contribution to the upper estimate for the local bending energy on a backward chart is \(+\epsilon\int G^2=o(1)\). Thus the same stopped construction works backward.

Here are the precise uniform properties needed below. Fix \(1<p<2,\ 0<\gamma<p\), and a tolerance \(\eta>0\). There is \(M_\eta\) such that, for any sufficiently small fixed \(h>0\), all but measure \(\eta+o(1)\) of either starting population admit a chart in either specified time direction with the following bounds. Call these starts good in that direction. In current coordinates \(x=Hs\) centered at the moving material point, \(0\le\theta\le h\), write \(K=k/H,\ G=\pm F/H,\ V_H=(K^2/2)T_{\rm tan}+K_xN\). On each dyadic \(A\ge1\),
\[
 \int_0^h|G(\theta,0)|^p d\theta\le M_\eta h,\qquad
 \int_0^h\int_{-A}^A|G|^pdx\,d\theta\le M_\eta h A^{1+\gamma}.
                                                                    \tag{2}
\]
Also \(\epsilon\iint_{[-A,A]}G^2=o(1)\), \(\epsilon\int |G(\theta,0)|^2=o(1)\), and the initial local squared spatial force \(\int_{-4}^4|\epsilon G(0,x)|^2dx=o(1)\). The little-oh bounds can be chosen uniform among good roots for each fixed \(A,h\). To see this, the summed expectations of the central and \(A^{-1-\gamma}\)-weighted stopped squared costs, after multiplication by \(\epsilon\), are \(O(h B_j^{-2})\); the initial cost is \(O(B_j^{-4})\). Use vanishing Markov thresholds for these costs and a fixed threshold times \(h\) for the total first group of \(p\)-costs. The forward or backward density ratio at the central material point stays in \([1/2,2]\) on the full chosen window by the [local energy and density argument](PhysicalForcedRectangularTube.md). It gives, for \(A\ge4\) fixed and \(u_A=\int_{-A}^A|G|dx\),
\[
      \sup_{[-A,A]}|V_H|\le C_\eta+C\epsilon u_A,\qquad
      \int u_A\le C_{\eta,A}h,\qquad \epsilon\int u_A^2=o(1).
                                                                    \tag{3}
\]
All \(M_\eta\) and first-group mean estimates are independent of \(h\) in its allowed range. The initial broad lower bound \(1/2\) still ensures a nonzero oscillator since its squared stress is bounded below at the center. Periodicity allows spatial extension of every chart. For any fixed chart radius the scaled period tends to infinity: Fenchel and the upper curvature-mean bound give \(L\ge2\pi/\sqrt C\).

For every sequence of good roots one can pass to a subsequence on which the local fields converge to the [rectangular modulation limit](ForcedRectangularModulation.md). This oscillator has a fixed stress norm \(v_0>0\), equal to its initial limiting central norm. Indeed the weak tested curvature has the initial oscillator as its trace, while a fixed positive amplitude has compact phase space. Its normal velocity is \(G=-d(\theta)\cdot N\) in the canonical frame. In particular the integral of \(KG\) over every full current spatial period is zero. A fixed radius \(A_0\) suffices to contain an entire period for all amplitudes \(v_0\in[1/2,32]\). The normals of a full period span the plane. By their explicit oscillator representation and compactness of this amplitude range, (2) gives
\[
                     h^{-1}\int_0^h |d(\theta)|^p d\theta\le C_\eta .
                                                                    \tag{4}
\]
Along the same subsequence \(\sup_{|x|\le A}||V_H(\theta,x)|-v_0|\to0\) in time measure for each fixed \(A\). To justify this claim, on the set \(\epsilon u_{2A}>1\) the time integral of \(\sup |K|^4\) tends to zero by (3), whereas on its complement \(K\) is uniformly bounded. Thus its strong local \(L^2\) convergence upgrades to strong \(L^4\). Since \(K_{xx}=-K^3/2\pm\epsilon G\), the second derivatives are bounded in local \(L^{4/3}\). Spatial integration by parts with an interior cutoff applied to the difference from the limiting \(K\) yields strong local \(L^2\) convergence of \(K_x\). Consequently the stress norms converge in spacetime measure. Their spatial oscillation on the window is at most \(\epsilon u_A\to0\) in time measure, proving the claim.

The central density factors \(g(\theta)=ds(t\pm\theta/H^2,q)/ds(t,q)\) have uniformly convergent subsequences on \([0,h]\). In fact \(|(\log g)_\theta|\le|K(\theta,0)G(\theta,0)|\), and (2)–(3) give a modulus \(C_\eta|\Delta\theta|^{1-1/p}+o(1)\): the additional term is bounded by \(C(\int u_4)^{1/2}(\epsilon\int|G(\cdot,0)|^2)^{1/2}\).

## Exact averaging over genuine material centers

Call a time and label \((v,z)\) a target at scale \(H\) when \(v\in{\rm supp}(w)\) and \(1\le |S(v,z)|/H^2\le16\). Give these targets measure \(H^2 ds(v,z)dv/P_j\); this is the narrow population just estimated. Draw \(x\) uniformly from \([-A,A]\) and \(\theta\) uniformly from \([0,h]\), independently, where \(A\ge A_0\) is fixed for now. For each target let \(q\) be the material label which at \(v\) lies a signed distance \(-x/H\) from \(z\), and set \(t=v-\theta/H^2\). At any fixed offsets and \(H\) the change of measure is exactly
\[
             ds(v,z)\,dv= ds(v,q)\,dv
                         =g_q(\theta)\,ds(t,q)\,dt .                   \tag{5}
\]
The first equality is arclength translation on a periodic slice. All contributing \(t\) belong to \(J\) for large \(j\).

Except for target-and-offset measure \(C\eta+C_{\eta,A}h+o(1)\), the resulting \((t,q)\) is a good forward broad start. First discard the bad backward targets, whose measure is at most \(\eta+o(1)\). In the backward chart of a good target the relative coordinate of the neighboring material point \(q\) evolves with velocity \(-\alpha\), with \(|\alpha(y)|\le\int_{-2A}^{2A}|KG|dx\) as long as \(|y|\le2A\). By (3) its time integral is \(C_{\eta,A}h+o(1)\). Choose \(h\) small enough that every initial offset \(|x|\le A\) stays within this larger chart. At all but \(o(1)\) of the time-offset fraction the entire chart has stress norm in \([1/2,32]\), since the backward limiting norm \(v_0\) lies in \([1,16]\). This conclusion is uniform for good backward targets at fixed \(A,h\): otherwise a contradicting subsequence of good targets has the compactness properties above. The resulting starts are consequently broad except on that vanishing set.

For each good backward target and each \(\theta\), the backward density ratio \(g_-(\theta,x)=ds(t,q)/ds(v,q)\) for the neighboring label with initial offset \(-x\) obeys
\[
 \int_{-A}^A|g_-(\theta,x)-1|\,dx
                   \le \int_0^h\int_{-2A}^{2A}|KG|\,dy\,d\theta'
                   \le C_{\eta,A}h+o(1).
\]
Indeed the absolute change of each moving material length element is bounded by the integral of \(|KG|ds\); the tracked interval stays in this chart by the displacement bound. Therefore except for offset fraction \(C_{\eta,A}h+o(1)\) the forward factor \(g_q(\theta)=g_-^{-1}\) in (5) is at most 2. On these remaining pairs the mass of those with a bad forward broad start is at most twice the forward bad starting measure by (5), integrating over the same independent uniform offsets and dropping the target restriction on the starting side. This proves the claimed coverage estimate.

On the target population \(K(v,z)=k/H\) is bounded, and the squared \(L^2\) norm of \(F/H\) in the population is bounded by \(C P_j^{-1}\int\int F^2\): only a bounded number of narrow bands overlap at any point. Cauchy–Schwarz therefore bounds the absolute flux on the missed target-and-offset pairs by
\[
                       C\sqrt{\eta+C_{\eta,A}h+o(1)} .                 \tag{6}
\]

## Flux on the covered targets

By (5), the flux captured from good broad forward starts is exactly their starting-measure integral of
\[
 \frac1{2Ah}\int_0^h\int_{-A}^A
      g_q(\theta)\,w(t+\theta/H^2)\,\psi(|V_H(\theta,x)|)
                            K(\theta,x)G(\theta,x)\,dx\,d\theta .       \tag{7}
\]
There is no backward-good restriction in (7); backward charts were used only to bound the omitted target mass. Along every convergent sequence of good forward charts the limit in (7) uses a spatially constant \(\psi(v_0)\), the uniform limit of \(g_q\), and constant \(w(t_*)\). To see passage of the velocity term, on the exceptional times \(\epsilon u_{2A}>1\) the total absolute mixed flux is \(o(1)\) by \(\int(1+\epsilon u_{2A})u_{2A}=o(1)\) on those times. Elsewhere \(K\) is uniformly bounded, it converges in measure and so does the stress cutoff. They give strong convergence in \(L^{p/(p-1)}\) after truncation, which pairs with weak \(G\in L^p\).

On each limiting time slice the integral of \(KG\) over complete periods vanishes. The remaining incomplete period has bounded length, and \(|KG|\le C|d(\theta)|\). Since \(g_q\le2\), (4) bounds the absolute value of every limit of (7) by \(C_\eta\|w\|_\infty/A\), uniformly in \(h\) and \(A\). By subsequence compactness this controls the limsup of the supremum of (7) over good starts at fixed \(A,h\). Their total starting measure is bounded independently of \(\eta,A,h,j\).

Given an error tolerance, first choose \(\eta\) small in (6), then \(A\) large compared to \(C_\eta\), and finally \(h>0\) small enough for the chart construction, displacement estimate, and the term \(C_{\eta,A}h\) in (6). Taking \(j\to\infty\) proves (1).

The conclusion extends to tests which are indicators of time subintervals, including endpoints of the original slab, by smooth approximation: the absolute contribution over any time set of measure \(e\) is at most \(C\sqrt e\) by Cauchy–Schwarz and the uniform mean-square-curvature bound. The same proof applies to moving interval endpoints after extracting convergent subsequences. If the bounded-stress parts of the energy vanish along the sequence on \(I\), choose \(B_j\to\infty\) slowly enough that \(\int_I\langle k^2{\bf1}_{|S|\le4B_j^2}\rangle dt\to0\). The signed flux from \(1-\zeta(|S|/B_j^2)\) then vanishes by Cauchy–Schwarz and the assumed total force budget. The remaining part vanishes by (1), and \(L'=\int kFds\) gives the asserted endpoint comparison.

## Unconditional angular cost on a physical RMS window

Put \(\mathcal A(t)=\int|k|ds\). For every \(a>0\) there is \(c_a>0\) with the following property on every smooth closed flow. Fix any starting time \(t_0\) and set \(m_0^2=2E(t_0)/L(t_0)\). Let \(J=[v,w]\subset[t_0,t_0+m_0^{-4}]\) be a physical subinterval through which the flow exists. Then
\[
 |L(w)-L(v)|\ge aL(t_0)
   \quad\Longrightarrow\quad
      m_0^4\int_J\mathcal A(t)dt\ \ge\ c_a\sqrt{2E(t_0)L(t_0)}.       \tag{8}
\]
For simplicity assume the flow exists throughout the displayed unit RMS window; for a shorter slab the same conclusion follows by smooth time approximation and sampling only on the available interior. In initial RMS units \(L(0)=P=\sqrt{2U_0}\), \(E(0)=P/2\). The physical inequalities \(\int_0^1(L')^2dt\le E(0)^2,\ E'=-D\) imply \(P/2\le L(t)\le3P/2,\ \langle k^2\rangle\le2,\ \int_0^1\langle F^2\rangle dt\le1\). Thus (1) needs no additional energy or regularity hypotheses on this window. If (8) were false along a sequence, then \(P_j^{-1}\int_J\mathcal A\,dt\to0\) in these units. On \(|S|\le4B^2\), \(k^2\le\sqrt8 B\,|k|\). Choosing \(B_j\to\infty\) slowly makes the low-stress bending mass divided by \(P_j\) tend to zero on \(J\). The preceding endpoint argument contradicts the assumed length gain or loss. When the terminal times of shorter slabs vary, pass to a subsequence on which the endpoints converge and ignore terminal strips of width \(\delta\) at cost \(O(\sqrt\delta)\), using the same physical bounds. If the limiting interval has zero duration the asserted length change is already impossible.

For example, on a flow with \(L(t)\sim\ell t^p\), \(1/4<p<1/2\), fix \(c,C_0>0\). At late times for which \(t^{1/2-p}E(t)/\ell\le C_0\), one necessarily has
\[
        \liminf_{\substack{t\to\infty\\t^{1/2-p}E(t)/\ell\le C_0}}
        \frac{\int_t^{(1+c)t}\mathcal A(r)\,dr}{\ell\,t^{p+3/4}}>0
\]
whenever such times go to infinity. Indeed, rescaling these starting curves by \(t^{-1/4}\) gives on the normalized slab \([1,1+c]\) lengths comparable to \(P=\ell t^{p-1/4}\), initial energy at most \(C_0P\), a uniformly bounded mean-square-curvature and integrated mean-square-force budget, and a relative length gain tending to \((1+c)^p-1>0\). Vanishing normalized angular mass again contradicts (1). This applies without assuming an energy asymptotic for the entire trajectory.

These are written mathematical arguments. The moving-chart compactness, the passage from selected windows to (1), and the physical endpoint consequence have not been checked in Lean.
