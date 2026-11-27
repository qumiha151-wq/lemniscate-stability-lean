# A forced rectangular-elastica limit selected on actual concentrating flows

Let a sequence of smooth closed planar free elastic flows be given on \([0,T]\), with one fixed spatial and temporal parabolic dilation per flow. Suppose \(L_j(t)\asymp P_j\to\infty\) uniformly, \(\sup_{j,t}\langle k_j^2\rangle<\infty\), and \(\sup_j\int_0^T\langle F_j^2\rangle dt<\infty\). Angle brackets are normalized arclength. Assume that on some compact interior time interval \(I\), for some \(b_j\to\infty\),
\[
                       \int_I\langle k_j^2{\bf1}_{|k_j|\ge b_j}\rangle dt\ge c>0 .
\]
Fix \(1<p<2\) and \(0<\gamma<p\). Then there are true material points and starting times in \(I\), scales \(H_j\to\infty\), and a fixed \(h>0\) such that in coordinates \(x=H_j s,\ \theta=H_j^2(t-t_j)\) around these points, the fields \(K_j=k_j/H_j,\ G_j=F_j/H_j\) admit subsequential limits on the whole spatial line for \(0<\theta<h\). Specifically \(G_j\rightharpoonup G\) locally in \(L^p\), \(K_j\to K\) locally in \(L^2\), \(K\) is nonzero, and
\[
 K_{xx}=-K^3/2,\qquad K_\theta=-G_{xx}+(\alpha K)_x,\qquad
     \alpha(\theta,x)=-\int_0^x K(\theta,y)G(\theta,y)dy .
                                                                    \tag{1}
\]
On every \(A\ge1\), \(\int_0^h\int_{-A}^A |G|^pdx\,d\theta\le C h A^{1+\gamma}\). The curve and the coordinate are actual throughout the construction. There is no proportionality hypothesis on \(F\). This selects one limiting observation window from energy that goes to large amplitudes; it does not identify the full flow's signed integral \(\int kFds\) with the integral on one such window.

## Selecting a true material chart at all spatial radii

Write \(S=(k^2/2)T+k_sN\), so \(S_s=FN\). Split the retained starting pairs into dyadic bands \(H^2\le |S|<4H^2\). They have \(H\ge a_j\to\infty\) and \(k^2\le8H^2\). Weight starting pairs by \(k^2dt\,ds(t)/L(t)\). The total weight is bounded above and is at least \(c\). For now use any small \(h>0\) less than the margin from \(I\) to the terminal time and at most one. As in the [stopped sampling construction](UniformMacroscopicDeficit.md), restrict observations to \(\sigma\le h\), the first time that the material density at the origin drops to \(1/2\), with the full window used if this does not happen. Set \(\epsilon=H^{-2}\).

For each dyadic \(A=2^n\ge1\) denote \(B_{q,A}=\int_0^\sigma\int_{-A}^A |G_j|^qdx\,d\theta\) and \(D_q=\int_0^\sigma|G_j(\theta,0)|^q d\theta\). Space is periodically extended for arbitrarily large \(A\). For \(B_{p,A}\), the part with \(|F|\le H\) has cost \(\le 2Ah\) at every start. On its complement the change of scales and two Fubini integrations bound the unweighted cost on a given band by \(C A h H^{-p}\int\langle |F|^p{\bf1}_{|F|>H}\rangle dt\). The alive labels satisfy \(ds(t_{\rm start})\le2ds(t_{\rm obs})\). Weighting on the band by \(k^2\le8H^2\), then summing \(\sum_{H<|F|}H^{2-p}\le C_p|F|^{2-p}\), gives total cost \(\le C A h\), including the low part. The same estimates hold for \(D_p\) with \(A\) replaced by \(1\). For the squared velocity, the energy-weighted total costs of \(\epsilon B_{2,A}\) and \(\epsilon D_2\) are at most \(CAh\sum_{H\ge a_j}H^{-2}=o(1)Ah\) and \(o(1)h\) respectively. The initial cost \(J_0=H^{-5}\int_{|s|\le4/H}F(t_{\rm start})^2ds\) has total weighted mean \(O(\sum_{H\ge a_j}H^{-4})=o(1)\).

Sum the space-window costs with weights \(A^{-1-\gamma}\). Markov's inequality applied to the resulting finite total and the positive retained weight gives a sequence of starts with
\[
 D_p+\sum_A A^{-1-\gamma}B_{p,A}\le C_c h,\qquad
 J_0+\epsilon D_2+\epsilon\sum_A A^{-1-\gamma}B_{2,A}\longrightarrow0 .
\]
The mean constants are independent of \(h\) in the indicated range, so \(h\) can be fixed sufficiently small below. The second estimate is required only for each fixed \(h>0\). The initial rescaled curves have \(1\le |S|/H^2\le4\) at their origins and initial stress oscillation \(o(1)\) on \([-4,4]\). Since \(K_{xx}=-K^3/2+\epsilon G_j\) and \(J_0=\|\epsilon G_j(0,\cdot)\|_{L^2(-4,4)}^2\), they have an initial nonzero \(C^1_{\rm loc}\) oscillator limit on this window.

## Keeping the same chart open and passing both equations to the limit

Write \(u_A(\theta)=\int_{-A}^A|G_j|dx\). The choices above give \(\int u_4\le C_c h,\ \int|G_j(\theta,0)|d\theta\le C_ch\), and \(\epsilon\int u_A^2=o(1)\) for each fixed \(A\). The true physical equations in these units have spatial force \(\epsilon G_j\) and normal speed \(-G_j\). Their bending density \(e=K_j^2/2\) satisfies
\[
 e_\theta=-\epsilon G_j^2+\partial_x\{(K_j)_xG_j-K_j(G_j)_x+\alpha e\},
 \qquad \alpha_x=-K_jG_j,\quad\alpha(0)=0 .
\]
Use the [weak-forcing moving cutoff](UniformMacroscopicDeficit.md) on \([-4,4]\), now with \(G_j\) itself in the flux and \(V=(K_j^2/2)T+(K_j)_xN\), \(V_x=\epsilon G_jN\). Its local spatial virial estimate is \(\sup_{[-4,4]}|V|\le C(1+m+\epsilon u_4)\) for the cutoff mass \(m=\int\chi e\). While \(m\le M\), \(|\alpha|\le C_M(1+\sqrt{\epsilon u_4})u_4\); use this as the inward motion bound for the cutoff. The total motion is \(O_c(h)+o(1)\), and \(m'\le C[(1+m)u_4+\epsilon u_4^2]\). Since the initial mass is bounded universally, choosing \(M\) with a fixed margin and then \(h>0\) small prevents either loss of the cutoff plateau or escape of \(m\). The central density satisfies
\[
 |\log g|\le C_M\int |G_j(\theta,0)|d\theta+
       C(\int u_4)^{1/2}(\epsilon D_2)^{1/2}\le C_c h+o(1).
\]
With \(h\) still smaller this ensures \(\sigma=h\). These constants concern the central window only. The same fixed \(h\) works on the full line: by \(V_x=\epsilon G_jN\), for every fixed \(A\ge4\)
\[
 \sup_{[-A,A]}|V|\le C+C\epsilon u_A,\qquad
 \int_0^h(\sup |K_j|^4+\sup |(K_j)_x|^2)d\theta=O_A(1).
\]

On the exceptional times \(\epsilon u_A>1\), the total first-power velocity and nonlinear flux are small, since
\[
 \int_{\epsilon u_A>1}(1+\epsilon u_A)u_A\,d\theta
                       \le 2\epsilon\int u_A^2d\theta=o(1).
\]
Off this set \(K_j,(K_j)_x\) are bounded uniformly on \([-A,A]\). Therefore \(|\alpha K_j|\le C(1+\epsilon u_A)u_A\), and \((K_j)_\theta=-(G_j)_{xx}+(\alpha K_j)_x\) gives \(L^1_\theta H^{-3}_x\) bounds locally. Together with \(L^2_\theta H^1_x\) compactness this gives local strong \(L^2\) convergence and, by interpolation, local strong \(L^q\) for \(q<4\). A nonzero initial curvature pairing persists for a positive time in the interior: on any interval of length \(\eta\) the tested force and nonlinear flux contribute \(O_A(\eta^{1-1/p})+o(1)\), by the selected \(p\)-moment bound and the exceptional-time estimate.

After deleting exceptional times the truncated \(K_j\) are uniformly bounded locally and converge strongly in all finite \(L^q\). Indeed the deleted spacetime measure tends to zero and the uniform \(L^4\) bound makes its \(L^2\) contribution negligible. The deleted parts of \(G_j\) converge weakly to zero in \(L^p\), by boundedness in that space and absolute continuity of the norm of any fixed dual test. For \(\alpha K_j\) the discarded contribution vanishes in \(L^1\) by the estimate above. Off the exceptional set the pairing of the nonlinear flux reduces by spatial Fubini to a weak \(G_j(\theta,y)\) paired with a product of the bounded truncated \(K_j(\theta,y)\) and a spatial primitive of a smooth test times the truncated \(K_j(\theta,x)\). This product converges strongly in \(L^{p/(p-1)}\). This passes the conservative equation to (1); the spatial equation follows from local strong \(L^3\) and \(\epsilon G_j\to0\). Diagonal extraction gives the same subsequence and time interval at all radii; lower semicontinuity and the dyadic moment bound give the stated growth for \(G\).

The selected solution of (1) meets the whole-line growth condition of the [weak rectangular modulation theorem](ForcedRectangularModulation.md), since \(1+\gamma<p+1\). Consequently it has fixed nonzero oscillator amplitude, its velocity is the normal component of a time-dependent translation in the canonical frame, and on almost every time slice \(\int_{x_0}^{x_0+P_K}\omega(|K|)KG\,dx=0\) for every full curvature period and every bounded Borel weight \(\omega\). The selection, spacetime compactness and modulation are written proofs and have not been checked in Lean. Passing from selected windows to the total mixed flux of a genuine trajectory requires a further argument.
