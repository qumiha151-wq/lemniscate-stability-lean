# Force dissipation and forward persistence at large length–energy records

Let \(X\) be a smooth global closed immersed planar free elastic flow. Use the material normal gauge \(X_t=-FN\), arclength \(s\), signed curvature \(k\), and
\[
 F=k_{ss}+\tfrac12k^3,\quad E=\tfrac12\int k^2ds,\quad
 D=\int F^2ds,\quad Y=\int F_{ss}^2ds,\quad U=EL.
\]
Every integral in space includes the whole period. On each slice \(E>0\), \(D>0\): a closed regular curve cannot be straight, and the dilation first variation gives \(\int F(X-p)\cdot N\,ds=-E\). The physical energy law is \(E'=-D\).

**Theorem.** There is a universal \(C\) such that
\[
 D'+Y\ \le\ C\big[(ED)^{2/3}+E^{1/4}D^{3/4}\big]D. \tag{1}
\]
Every such trajectory satisfies
\[
 D(t)\longrightarrow0,\qquad \int_1^\infty D^{-2/3}Y\,dt<\infty,\qquad
 \int_1^\infty\|F_s\|_\infty^{4/3}\,dt<\infty. \tag{2}
\]
In particular the maximum material tangent angular speed has cumulative integral \(o(t^{1/4})\). A single bound on the integral in (2) need not give a finite integral of the unsquared angular speed over infinite time.

The bounds have a universal restart form. For any initial time \(s_0\), put \(e=E(s_0)\) and \(s_1=s_0+e^{-4}\). With scale-independent \(C\),
\[
 \sup_{t\ge s_1}D(t)\le Ce^5,\qquad
 \int_{s_1}^\infty D^{-2/3}Y\,dt\le Ce^{5/3},\qquad
 \int_{s_1}^\infty\|F_s\|_\infty^{4/3}\,dt\le Ce^{4/3}. \tag{2a}
\]

In the same units the normal speed satisfies \(\int_{s_1}^\infty\|F\|_\infty^{12/7}\,dt\le C e^{8/7}\). In particular the entire material immersion obeys
\[
        \sup_u |X(t,u)-X(0,u)|=o(t^{5/12}).
\]
Its distance from any fixed origin, its enclosing radius and the norm of its arclength centroid have the same upper growth estimate.

**Forward record window.** At any positive time \(t_0\) with \(U'(t_0)\ge0\), write \(H=U(t_0)\). Dilate space by \(E(t_0)\), time by \(E(t_0)^4\), and set the new time origin at \(t_0\). This constant dilation preserves the physical equation. For all sufficiently large \(H\), the following estimates hold throughout \(0\le t\le cH^{4/3}\) in these units, with universal constants:
\[
 D(t)\le4H^{-2},\quad 1-CH^{-2/3}\le E(t)\le1,\quad |L(t)-H|\le CH^{1/3},
 \quad \int_0^{cH^{4/3}}Y(t)\,dt\le CH^{-2}. \tag{3}
\]
On the same interval,
\[
 \int\|F_s\|_\infty dt+\int\|kF\|_\infty dt\le CH^{-1/6},
 \qquad \int\|F\|_\infty dt\le CH^{1/6}. \tag{4}
\]
Thus the tangent directions at all material labels and their arclength density ratios stay uniformly close to their initial values. Each material point moves at most \(CH^{1/6}\), small compared with the length scale \(H^{1/3}\) on which the curvature is bounded. These are forward windows starting at the specified growing record, even if the length–energy product subsequently decreases.

## The force derivative and elastic stress

The metric evolution gives \((ds)_t=kFds\), \([\partial_t,\partial_s]=-kF\partial_s\), and \(k_t=-F_{ss}-k^2F\). Commuting twice and differentiating \(k^3/2\) yields
\[
 F_t=-F_{ssss}-\tfrac52 k^2F_{ss}-5kk_sF_s
       -(3k_s^2+4kk_{ss}+\tfrac32k^4)F .
\]
In \(D'=2\int FF_tds+\int kF^3ds\), the integrated derivative of \(k^2\) cancels the first-order term in \(F_t\). Substituting \(k_{ss}=F-k^3/2\) gives
\[
 D'=-2Y+5\int k^2F_s^2-6\int k_s^2F^2+\int k^4F^2-7\int kF^3 .
\]
Now integrate \(\int kk_{ss}F^2\) by parts in \(\int kF^3=\int kk_{ss}F^2+\tfrac12\int k^4F^2\). Periodicity gives the exact second expression
\[
 D'=-2Y+5\int k^2F_s^2+\int k_s^2F^2
       +14\int kk_sFF_s-\tfrac52\int k^4F^2 .
\]
Write \(M=\|k\|_\infty\), \(S=\|k_s\|_\infty\). The mixed term is at most \(7\int k_s^2F^2+7\int k^2F_s^2\). Since \(\int F_s^2=-\int FF_{ss}\le\sqrt{DY}\), completing one square gives
\[
           D'+Y\le(36M^4+8S^2)D.                         \tag{5}
\]

The already established closed-curve stress inequality is \(M^6\le 2^{24}ED\). To estimate \(S\), let \(W=(k^2/2)T+k_sN\). Its Frenet derivative is \(W_s=FN\), hence \((|W|^2)_s=2k_s F\). Choose an arclength point of maximum \(|k|=M>0\); there \(k_s=0\) and \(|W|^2=M^4/4\). Integrating to any other point along at most one period gives
\[
 S^2\le M^4/4+2\|k_s\|_2\sqrt D,\qquad
 \|k_s\|_2^2=\tfrac12\int k^4-\int kF\le EM^2+\sqrt{2ED}.
\]
Therefore \(S^2\le C[(ED)^{2/3}+E^{1/4}D^{3/4}]\). Equation (5) now implies (1). No bound on total length or on the number of curvature zeros is used. [Formal material stress inequality](../../LengthGrowth/ActualFlow/ArclengthCoercivity.lean)

## Integrability on one complete trajectory

Write \(E_0=E(0)\). Since \(\int_0^\infty D\,dt\le E_0\), \(D\) takes arbitrarily small values arbitrarily late. Fix \(\eta>0\). On \(\eta/2\le D\le\eta\), (1) bounds \(D'\) from above by a finite constant depending on \(\eta,E_0\) only. Every passage from \(\eta/2\) to \(\eta\) costs a positive amount of physical time and of \(\int D\). Infinitely many passages are impossible; hence \(D(t)\to0\).

Once \(D\le E_0^5\), (1) yields \(D'+Y\le C E_0^{2/3}D^{5/3}\). Multiply by \(D^{-2/3}\), integrate from \(s\) to \(t\) on that tail, and use \(E'=-D\) to obtain
\[
 \int_s^t D^{-2/3}Y\,dr\le3[D(s)^{1/3}-D(t)^{1/3}]
             +C E_0^{2/3}[E(s)-E(t)].                    \tag{6}
\]
On earlier compact positive-time intervals smoothness and strict positivity of \(D\) give finite integrals. For the last assertion of (2), periodic \(F_s\) has mean zero and hence a zero on each slice. Integrating \((F_s^2)_s\) from that zero and using \(\int F_s^2\le\sqrt{DY}\) gives \(\|F_s\|_\infty^2\le2D^{1/4}Y^{3/4}\), with no period-dependent remainder. Consequently
\[
 \int_s^t\|F_s\|_\infty^{4/3}dr
 \le 2^{2/3}\left(\int_s^tD\,dr\right)^{1/2}
                 \left(\int_s^tD^{-2/3}Y\,dr\right)^{1/2}.
\]
Splitting off a fixed initial interval, applying Hölder to the remainder, and then sending the split time to infinity gives \(\int_1^t\|F_s\|_\infty=o(t^{1/4})\). The material tangent satisfies \(T_t=-F_sN\).

For (2a) restart and dilate to \(s_0=0,\ E_0=1\). Some \(q\in[0,1]\) has \(D(q)\le1\), by the energy identity. On each component of \(\{t>q:D(t)>1\}\), (1) gives \((D^{1/4})'\le CD\). The component starts with \(D=1\); integrating and using \(\int_q^\infty D\le1\) gives \(D\le(1+C)^4\). In particular \(D'+Y\le C'D^{5/3}\) with a universal constant throughout \(t\ge q\). Integrating from \(q\) gives (6) with a universal right-hand bound, and the angular estimate follows by the preceding interpolation. Returning to the original units gives (2a), including the three indicated powers of the energy. If the restart is at the original initial time, smoothness and the energy identity from that time suffice.

For the normal-speed estimate, the same periodic interpolation starting from a point where \(F^2\le D/L\) gives \(\|F\|_\infty\le \sqrt{D/L}+\sqrt2 D^{3/8}Y^{1/8}\). Fenchel and Cauchy–Schwarz give \(EL\ge2\pi^2\), and the closed-curve dilation virial gives \(D L^3\ge4\pi^2 E^2\); thus \(D L^5\ge16\pi^6\) and \(\sqrt{D/L}\le C D^{3/5}\). In the restarted energy-one variables \(D\) is uniformly bounded for \(t\ge1\), so \(\int_1^\infty D^{36/35}\le C\int_1^\infty D\le C\). The other summand raised to the \(12/7\)-th power is a constant times \(D^{11/14}(D^{-2/3}Y)^{3/14}\); its integral is uniformly bounded by (2a) and Hölder. Rescaling proves the stated rate budget. Splitting the integral of \(\|F\|_\infty\) at a large fixed time and applying Hölder to the tail as above yields \(o(t^{5/12})\). In the normal material gauge this bounds displacement uniformly in the label; the bounds for the whole image and its centroid follow. [Formal closed-curve virial inequality](../../LengthGrowth/ActualFlow/SharpVirial.lean)

## Persistence after a growing record

In the stated constant energy-normalization \(E(0)=1,\ L(0)=H\). The genuine first variations \(L'=\int kF,\ E'=-D\) and \(U'(0)\ge0\) give \(HD(0)\le\sqrt{2D(0)}\); hence \(D(0)\le2H^{-2}\). As long as \(D\le4H^{-2}\le1\), (1) and \(E\le1\) give \(D'+Y\le C(4H^{-2})^{5/3}\). For a sufficiently small universal \(c>0\), integration up to \(cH^{4/3}\) precludes the first hit of \(4H^{-2}\), proving the uniform bound. Integrating (1) with \(Y\) retained gives the last estimate in (3); integrating the energy identity and \(|L'|\le\sqrt{2ED}\) gives the remaining ones. In the variable energy clock \(\sigma=\int E^4dt\) the same window has comparable duration, since \(E=1+O(H^{-2/3})\). Equivalently \(d=D/E^5\) satisfies \(d_\sigma\le C d^{5/3}\) wherever \(d\le1\), by (1) and the chain rule.

By the stress estimate, \(M\le CH^{-1/3}\) throughout this forward window. For \(\|F\|_\infty\), start at a point with \(F^2\le D/L\) and integrate \((F^2)_s\); this gives \(\|F\|_\infty\le\sqrt{D/L}+\sqrt2 D^{3/8}Y^{1/8}\). Set \(h=cH^{4/3}\). The zero-mean derivative estimate and Hölder give
\[
 \int_0^h\|F_s\|_\infty\le C(\sup D)^{1/8}h^{5/8}\Big(\int_0^hY\Big)^{3/8}
 \le CH^{-1/6}.
\]
Likewise \(\int_0^h\|F\|_\infty\le h\sqrt{\sup D/\inf L}
 +C(\sup D)^{3/8}h^{7/8}(\int_0^hY)^{1/8}\le CH^{1/6}\). Multiplying by \(\sup M\) controls the change of \(\log |X_u|\) at every material label. This proves (4).

These windows constrain the subsequent evolution of any high-product record of a single flow. They allow slow accumulation on longer clocks; the existence or exclusion of one trajectory with unbounded \(EL\) is still open. [Miura and Wheeler, free elastic flow for closed planar curves](https://arxiv.org/abs/2404.12619)

## Verification scope

The module \(\texttt{ForcePersistence}\) defines \(Y\) by two actual arclength derivatives of the position-defined force. It checks (6) on a finite interval under the stated force-rate inequality, including differentiation of the actual dissipation and the physical energy law. Its record theorem checks the forward bound on \(D\) and the lower bound on \(E\) from the genuine product-record condition and the small-dissipation rate. The module \(\texttt{ForceAngularSpeed}\) checks \(|F_s(u)|^8\le16DY^3\) at every material label in a full period of any regular smooth flow slice, with arbitrary speed and multiplicity. The geometric derivation of (1) from the force evolution, the global tail and restart arguments, and the full material estimates (4) are the mathematical proofs above. [ForcePersistence.lean](../../LengthGrowth/ActualFlow/ForcePersistence.lean) · [ForceAngularSpeed.lean](../../LengthGrowth/ActualFlow/ForceAngularSpeed.lean)
