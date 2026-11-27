# Vanishing length change on slow windows with bounded rescaled action

Consider any sequence of genuine smooth closed planar free elastic flows, with physical intervals \([t_j,t_j']\), and write \(L_0=L(t_j)\), \(E_0=E(t_j)\), \(E_1=E(t_j')\), allowing the flows to vary. Assume
\[
 m_0^2=2E_0/L_0,\qquad T_j=m_0^4(t_j'-t_j)\to\infty,\qquad
 \sup_j\,T_j(1-E_1/E_0)<\infty .
                                                                    \tag{1}
\]
Then, without any assumption on the intervening lengths,
\[
           \sup_{t_j\le t\le t_j'}\left|\frac{L(t)-L_0}{L_0}\right|
                                  \longrightarrow0.                    \tag{2}
\]
In particular, if \(t_j'\) is the first exit from a fixed relative length neighborhood \(((1-a)L_0,(1+a)L_0)\), \(0<a<1\), and \(T_j\to\infty\), then \(T_j(1-E_1/E_0)\to\infty\). No bound on energy–length product, curvature derivatives, angle variation, or covering multiplicity is assumed.

## A geometric zero-flux limit at small force scale

We first prove a geometric statement on a fixed time slab \([0,1]\). Suppose closed smooth curves have physical normal velocity \(-G_j N\) in that time variable and
\[
 k_{ss}+k^3/2=\delta_j G_j,\qquad \delta_j\to0,\quad\delta_j>0 .
\]
Assume \(L_j\asymp P_j\to\infty\), \(\sup_{j,t}\langle k_j^2\rangle\le C\), and \(\sup_j\int_0^1\langle G_j^2\rangle dt\le C\). Then for each time subinterval \(I\subset[0,1]\)
\[
               \frac1{P_j}\int_I\int k_jG_j\,ds\,dt\longrightarrow0 .
                                                                    \tag{3}
\]

To see this, fix \(a>0\) and use dyadic spatial scales \(H=a2^n,\ n\ge0\), with the same smooth stress partition as in the [large-stress flux proof](HighStressSignedFlux.md). Set \(S=(k^2/2)T+k_sN\). A selected observation now has spatial coordinate \(x=Hs\), time increment \(\theta/H^2\), curvature \(K=k/H\), normal force \(G=G_j/H\), and
\[
              K_{xx}+K^3/2=\epsilon G,\qquad \epsilon=\delta_j/H^2 .
\]
For fixed \(a\), all the selected spatial parameters \(\epsilon\) tend uniformly to zero, even for bounded \(H\), and their spatial periods \(HL_j\) tend uniformly to infinity. We give the changes needed for the two-direction coverage proof; the interval parameters and cutoffs are otherwise the same.

* The starting weights \(H^2dt\,ds/P_j\) on the broad ranges remain summable because \(S_s=\delta_jG_jN\). The stress-weight estimate now gives \(\langle (1+|S|^2)^{1/2}\rangle\le C(1+\langle k^2\rangle+\delta_j\langle|G_j|\rangle)\).
* For \(1<p<2\), the stopped \(p\)-cost sum uses \(\sum_{H<|G_j|}H^{2-p}\le C_p|G_j|^{2-p}\) at any initial scale \(a\). The total squared cost weighted by \(\epsilon\) is \(O_A(h\delta_j\sum_{H\ge a}H^{-2})=O_{A,a}(h\delta_j)\). The initial squared spatial-force cost is \(O(\delta_j^2\sum_{H\ge a}H^{-4})=O_a(\delta_j^2)\). Both vanish. The backward energy sink has the opposite sign, and its integral is still bounded by the vanishing \(\epsilon\)-weighted cost.
* With these estimates the local bounds, central density comparison, weak compactness, spatially constant limiting stress amplitude and purely translational limiting normal speed follow exactly as in the [actual tube selection](PhysicalForcedRectangularTube.md) and [modulation proof](ForcedRectangularModulation.md). The signed flux on each full spatial period is zero. For a target supported with a time margin \(d>0\), choose the observation duration \(h\) also smaller than \(a^2d/2\), so fixed-offset time translates remain within the slab. In the forward chart integral the weight \(w(t+\theta/H^2)\) need not converge to a constant in time. Its subsequential uniform limit is \(w(t_*+\theta/H_*^2)\), with \(H_*\in[a,\infty]\), and is spatially constant. This is all that the spatial period cancellation requires.
* The inverse chart and its neighboring material labels have the same displacement and density bounds. The change of variables \(ds(v,z)\,dv=g_q(\theta)ds(t,q)\,dt\) is unchanged. Thus the discarded target mass, period averaging and order of limits (bad-measure tolerance, spatial radius, small observation duration) again give
  \[
   P_j^{-1}\int w(t)\int \zeta(|S|/a^2)\,k_jG_j\,ds\,dt\longrightarrow0 .
  \]
All these steps are for fixed \(a\). On the support of the complementary cutoff \(1-\zeta(|S|/a^2)\), \(|k|\le\sqrt8\,a\). Hence its absolute contribution is at most \(C_w a\) by the assumed squared-speed budget. Send \(a\downarrow0\) to conclude (3) first for smooth time tests. The contribution on any time set of measure \(e\) is bounded by \(C\sqrt e\), so interval indicators, including the endpoints, follow. No component of the signed flux, of bounded or unbounded stress amplitude, remains in (3).

## Application to physical time

On each given flow dilate space by \(m_0\) and time by \(m_0^4\). Its initial length and energy become \(P_j=\sqrt{2E_0L_0}\) and \(P_j/2\). Let \(d=1-E_1/E_0\). Under (1), \(d\to0\), and the scalar physical secant gives \(L/P_j\le1+\tfrac12\sqrt{2T_j d}\le C\) on the whole normalized interval. There \(E\ge P_j/4\) for large \(j\). The [closed-curve dilation inequality](../../LengthGrowth/ActualFlow/SaturationSupport.lean) implies \(D L^3\ge E^2\): take as origin any point of the current curve, so its maximum distance is at most \(L\), and use \(|\int F(X-O)\cdot N\,ds|=E\). Hence \(D\ge c/P_j\) throughout, and integration gives \(P_j^2 d\ge c T_j\). Thus \(P_j\to\infty\) follows from (1).

First consider intervals on which \(L/P_j\) is also bounded away from zero. Run time \(\theta\) from \(0\) to \(1\) by setting the normalized physical time equal to \(T_j\theta\), keeping the spatial normalization fixed. If \(F\) is the elastic force in the intermediate RMS units, the velocity on the unit slab is \(-G_jN\) with \(G_j=T_j F\), so \(\delta_j=1/T_j\). From energy monotonicity and length comparability the mean curvature squared is uniformly bounded. Write \(c>0\) for the comparability constant from below. The true energy identity gives
\[
  \int_0^1\langle G_j^2\rangle d\theta
       \le \frac{T_j}{cP_j}\int_0^{T_j}\int F^2ds\,dr
       = \frac{T_j}{2c}(1-E_1/E_0).
\]
Thus (1) gives the hypotheses of (3), and \(L_\theta'=\int kG_jds\) proves the endpoint assertion under comparability. For unrestricted intervening lengths, if (2) failed there would be a subsequence with a first exit by some fixed fraction \(0<a<1\). Write \(T_*\le T_j\) for its initial RMS duration and \(d_*=1-E(t_*)/E_0\). Now \(d_*\le1-E_1/E_0\to0\), and the physical secant inequality gives \(4a^2\le T_*[1-(E(t_*)/E_0)^2]\), so \(T_*\to\infty\). Moreover \(T_* d_*\le T_j(1-E_1/E_0)\) stays bounded. Until that first exit lengths are comparable by definition, contradicting the endpoint assertion. This proves (2) uniformly throughout. For any sequence of first exits with \(T_j\to\infty\), failure of the claimed cost divergence would similarly give a bounded subsequence.

For a fixed-fraction exit this also yields the following direct strengthening of the scalar energy secant estimate on such long normalized windows:
\[
      \frac{|L(t_j')-L_0|}
      {\sqrt{(t_j'-t_j)(E_0^2-E_1^2)}}\longrightarrow0 .
\]
The square of this ratio is \(4a^2/\{T_j[1-(E_1/E_0)^2]\}\). Cauchy–Schwarz alone gives an upper bound of one. The geometric conclusion still allows indefinitely slow successive growth at a larger rescaled action cost.

## A constraint on any positive limiting bending energy

If a smooth global flow has \(E_\infty=\lim_{t\to\infty}E(t)>0\), then necessarily
\[
             \limsup_{t\to\infty}
               t^{1/11}(\log t)^{6/11}\,[E(t)-E_\infty]=\infty.        \tag{4}
\]
No length asymptotic is assumed. To prove it suppose \(g(t)=E(t)-E_\infty\le C t^{-1/11}(\log t)^{-6/11}\) eventually, and define \(H(t)=t^{5/11}(\log t)^{-3/11}\). The energy secant on every \([v,2v]\) is
\[
 |L(w)-L(v)|\le \sqrt{(w-v)[E(v)^2-E(w)^2]}
                \le C\sqrt{v g(v)}\le C H(v)\qquad(v\le w\le2v).
\]
Summing dyadically gives \(L(t)=O(H(t))\) since the envelope has positive power exponent. In fact \(L(t)=o(H(t))\). Otherwise choose \(t_j\to\infty\) with \(L(t_j)\ge b H(t_j)\). Fix a sufficiently small \(0<\theta<1\) so that the preceding upper bound yields \(L(\theta t_j)<L(t_j)/2\) for large \(j\). Let \(s_j\ge\theta t_j\) be the last time before \(t_j\) when \(L(s_j)=L(t_j)/2\), and \(r_j\le t_j\) the first subsequent time when \(L(r_j)=L(t_j)\). On this interval \(L\) stays between these two values, and \(E(s_j)L(s_j)\to\infty\). The fractional energy loss tends to zero, forcing the normalized time of this doubling to tend to infinity by the secant inequality. Yet its normalized time times its fractional loss is at most \(C t_j g(\theta t_j)/L(t_j)^2=O(1)\), contradicting (2).

Let \(M=\sup |k|\), and \(R(t)\) be the largest distance to a fixed origin. On \([v,2v]\) the [physical stress and location estimates](../SpatialLocalization/ExponentialLocalization.md) give
\[
 \int_v^{2v} M^2 dr \le C v^{2/3}(E(v)^2-E(2v)^2)^{1/3}
           \le C v^{7/11}(\log v)^{-2/11}.
\]
Dyadic summation gives the same bound through time \(t\), with \(v\) replaced by \(t\). The finite-time exponential position moment then bounds
\[
 R(t)^2 \le C\big(1+t^{1/2}(\log t)^{3/2}
                         +(\log t)\textstyle\int_0^t M^2dr\big)
                =O\big(t^{7/11}(\log t)^{9/11}\big).
\]
The actual dilation identity \(\left|\int F(X-O)\cdot N\,ds\right|=E\) and Cauchy–Schwarz imply \(D\ge E_\infty^2/(L R^2)\). Integrating over \([t,2t]\) and using \(L=o(t^{5/11}(\log t)^{-3/11})\) yields \(g(t)/(t^{-1/11}(\log t)^{-6/11})\to\infty\), contradicting the original upper bound. This proves (4). It excludes fast convergence to a positive plateau and does not establish that every limiting energy is zero.

There is also an estimate at every sufficiently large time rather than just a limsup:
\[
                   t^{1/10}(\log t)^{3/5}g(t)\longrightarrow\infty .
                                                                    \tag{5}
\]
The universal bounds \(L(t)=o(\sqrt t)\) and \(R(t)=O(t^{1/3}\sqrt{\log t})\) first give the rough \(g(t)\ge c t^{-1/6}/\log t\) by integrating \(D\ge E_\infty^2/(LR^2)\) on \([t,2t]\). Here the little-oh length bound also follows directly from \(\int_0^\infty(L')^2dt<\infty\) by splitting the time secant at a fixed late time. In particular \(\log(t/g(t))=O(\log t)\).

Choose \(S=t/g(t)\), in fixed units, and take \(t\) sufficiently large that \(S>2t\). Then \(\sup_{[t,2S]} L=o(\sqrt t)\). Otherwise along a sequence, for some \(b>0\), the flow starting with \(L(t)=o(\sqrt t)\) reaches \(b\sqrt t\) there. Between its last preceding hit of \(b\sqrt t/2\) and its first hit of \(b\sqrt t\), the product tends uniformly to infinity, the fractional energy loss tends to zero, and the secant implies a divergent RMS duration. Yet the duration times the fractional energy loss is at most \(C Sg(t)/t=C\), contradicting the endpoint statement proved above.

On \([t,2S]\) the stress bound gives \(\int_t^{2S}M^2dr\le C S^{2/3}g(t)^{1/3}\). In the [restarted position moment](PhysicalPowerDeficit.md) take \(a=t^{-1/3}g(t)^{1/6}\sqrt{\log t}\). Then \(a^2\int_t^{2S}M^2dr=O(\log t)\), \(a^4 S=(t g(t))^{-1/3}(\log t)^2=o(1)\), and \(\log[(E(t)+a^2L(t))/(ma^2)]\le C\log t\) for the fixed positive lower arclength \(m\). Absorbing the starting radius \(R(t)\) gives
\[
                \sup_{[S,2S]} R\le C t^{1/3}g(t)^{-1/6}\sqrt{\log t}.
\]
Integrating the dilation bound on \([S,2S]\) and using the strict length estimate on this window gives
\[
     \frac{g(t)}{\,t^{-1/6}g(t)^{-2/3}/\log t\,}\longrightarrow\infty .
\]
Raising the resulting estimate for \(g(t)^{5/3}\) to the power \(3/5\) is (5). The distinct exponents in (4) and (5) reflect that a uniform upper bound on the past energy tail was assumed only in the contradiction for (4).

The manuscript is a written proof with no Lean verification of these new assertions.
