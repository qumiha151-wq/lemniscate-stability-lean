# Quantitative energy corrections for power-law length

Consider a smooth global closed planar free elastic flow. Write \(E=\int k^2ds/2\), \(L=\int ds\), \(D=\int F^2ds\), \(U=EL\), and \(F=k_{ss}+k^3/2\). If \(\delta(t)=\int_t^\infty L^{-4}ds\) is finite, set
\[
 \Delta(t)=U(t)-\delta(t)^{-1/2},\qquad A(t)=\delta(t)-U(t)^{-2}.
\]
The variable of integration in \(\delta\) is physical time. A multiplicative comparison \(f\asymp g\) means eventual two-sided inequalities with fixed positive constants. All constants below may depend on the flow and the constants in these comparisons.

1. If \(L(t)\sim\ell t^\alpha\), with \(\ell>0\) and \(1/4<\alpha<1/2\), then
   \[
      \liminf_{t\to\infty} U(t)\sqrt{\delta(t)}
        \ \ge\ \frac{\alpha}{\sqrt{(1-2\alpha)(4\alpha-1)}} .
                                                               \tag{1}
   \]
   This number exceeds one for every \(\alpha\ne 1/3\).
2. If \(L(t)\asymp t^{1/3}\), including cases where \(L(t)/t^{1/3}\) has no limit, then for all sufficiently large \(t\),
   \[
                 \Delta(t)\ \ge\ c\,\frac{t^{1/30}}{\log t}.
                                                               \tag{2}
   \]
   This assumes no energy decay rate.
3. If furthermore \(E(t)\asymp t^{-1/6}\), the estimate improves to
   \[
                 \Delta(t)\ \ge\ c\,\frac{t^{1/9}}{\log t}.     \tag{3}
   \]
   In particular the two asymptotics \(L(t)=\ell t^{1/3}(1+\varepsilon_L(t))\) and \(E(t)=(\ell/\sqrt3)t^{-1/6}(1+\varepsilon_E(t))\) cannot both have errors \(o(t^{-1/18}/\log t)\). These are necessary conditions on hypothetical growing flows. The possibility of fourth-root growth on every individual flow remains open.

## The scalar energy comparison

Since \(E'=-D,\ L'=\int kF\,ds\), one has \(- (E^2)'\ge (L')^2\). Fix \(b>1\) and any partition \(1=s_0<\cdots<s_n=b\). The Cauchy–Schwarz inequality on each physical subinterval gives
\[
 t^{1-2\alpha} E(t)^2\ge
 \sum_{i=1}^n
 \frac{(t^{-\alpha}L(ts_i)-t^{-\alpha}L(ts_{i-1}))^2}{s_i-s_{i-1}} .
\]
For fixed partition the right side converges to the same expression with \(s\mapsto\ell s^\alpha\). Using partitions with mesh tending to zero gives the integral of \(\ell^2\alpha^2s^{2\alpha-2}\) from \(1\) to \(b\), by uniform continuity of the derivative on this interval. Taking \(b\to\infty\) proves \(\liminf t^{1/2-\alpha} E(t)\ge\ell\alpha/\sqrt{1-2\alpha}\). Now \(\delta(t)\sim\ell^{-4}t^{1-4\alpha}/(4\alpha-1)\), which gives (1). The strict comparison follows from \(\alpha^2-(1-2\alpha)(4\alpha-1)=(3\alpha-1)^2\).

## Physical estimates on a restarted interval

Put \(\eta=LU'/E^3,\ \rho=1/2-\eta\). The exact square completion gives
\[
 A(t)=2\int_t^\infty \rho(s)L(s)^{-4}\,ds,\qquad
 0\le A(t)\le 2\delta(t)^{3/2}\Delta(t).
                                                               \tag{4}
\]
These statements use the finite terminal clock, which follows here from \(L\asymp t^{1/3}\). The second follows by multiplying \(\Delta\) by \((U\sqrt\delta+1)/(U^2\delta)\le2\). The dilation support identity on each physical slice gives
\[
                  \rho(s)\ge\frac{L(s)}{4E(s)R(s)^2},
                                                               \tag{5}
\]
where \(R(s)\) is the maximum distance of the slice to one fixed origin. [Finite clock identity](FiniteClockGrowthCorrection.md) · [Actual support and radius estimate](../../LengthGrowth/ActualFlow/SaturationRadius.lean)

Let \(M(s)=\sup|k(s,\cdot)|\). The physical stress estimate \(M^6\le 2^{24} ED\) implies
\[
 \int_v^w M^2\,ds\le C(w-v)^{2/3}(E(v)^2-E(w)^2)^{1/3}.       \tag{6}
\]
Write \(m=\min(1,2\pi^2/E(0))\). The exponential position moment, restarted at any \(v\), gives for \(s\ge v\) and \(0<a\le1\)
\[
 R(s)\le R(v)+m+
 \frac{\log[(E(v)+a^2L(v))/(ma^2)]
       +256\big[a^4(s-v)+a^2\int_v^s M(r)^2dr\big]}{a}.       \tag{7}
\]
Indeed every later slice has length at least \(m\), by the universal bound \(EL\ge2\pi^2\) and monotonicity of \(E\). The initial value of the exponential moment for each fixed direction is at most \((E(v)+a^2L(v))\exp(aR(v))\). This proves the restart with the same \(m\). In particular the unconditional position estimate gives \(R(v)=O(v^{1/3}\sqrt{\log v})\) for large \(v\). [Material localization and its finite-time moment inequality](../SpatialLocalization/ExponentialLocalization.md)

Suppose on \([v,2S]\), \(v\) large and \(S\ge v\), that \(E(r)\le C_0r^{-1/6}\). Sum (6) over the dyadic intervals starting at \(v,2v,4v,\ldots\) and the last truncated subinterval. Each contribution is bounded by a constant times the left endpoint to the power \(2/3-1/9=5/9\). Hence \(\int_v^{2S}M^2\,dr\le C S^{5/9}\), with \(C\) independent of the starting time if \(C_0\) is uniform. In (7) take \(a=S^{-5/18}\sqrt{\log S}\). The logarithmic term is \(O(\log S)\) since \(L(v)=O(v^{1/3})\) and \(E(v)\le E(0)\). The last two terms in its numerator are also \(O(\log S)\). Consequently
\[
  \sup_{S\le s\le 2S}R(s)\le R(v)+C S^{5/18}\sqrt{\log S}.     \tag{8}
\]

## Critical length with and without an energy law

For (3), fix a sufficiently large \(v\) so the power bounds hold throughout its future. Then (8) with \(S=t\) and (5) imply \(\rho(s)\ge c t^{-1/18}/\log t\) on \(t\le s\le2t\). Since \(L(s)^{-4}\ge c t^{-4/3}\), (4) gives \(A(t)\ge c t^{-7/18}/\log t\). Also \(\delta(t)\asymp t^{-1/3}\), so (3) follows by (4). If both stated relative errors were little-oh of \(w(t)=t^{-1/18}/\log t\), then integration of \(L^{-4}\) would give \(\delta(t)=3\ell^{-4}t^{-1/3}(1+o(w(t)))\), since \(w\) decreases. The two leading terms in \(\Delta(t)\) would cancel to \(o(t^{1/9}/\log t)\), contradicting (3).

For (2), fix any sufficiently large \(t\) and put \(S=t^{6/5}\). If \(A(t)>t^{-7/15}/\log t\) then (4) already gives the required estimate. In the other case, for all \(s\in[t,2S]\), (4) and the length bounds imply
\[
 0\le A(s)\le A(t)\le t^{-7/15}/\log t
       \le\tfrac12\delta(s)
\]
for large \(t\), because \(\delta(s)\ge c S^{-1/3}=c t^{-2/5}\). Thus \(U(s)^{-2}=\delta(s)-A(s)\asymp s^{-1/3}\), and \(E(s)\asymp s^{-1/6}\) there with constants independent of \(t\). Apply (8) with \(v=t\). The unconditional \(R(t)\) term can be absorbed since \(S^{5/18}=t^{1/3}\). On \([S,2S]\) it follows again that \(\rho(s)\ge c S^{-1/18}/\log S\). By (4),
\[
         A(t)\ge c S^{-7/18}/\log S
              \ge c' t^{-7/15}/\log t.
\]
This bound holds in both cases. Divide by \(2\delta(t)^{3/2}\le C t^{-1/2}\) to obtain (2).

The derivation above is a written proof. The free-flow energy laws, the physical support inequality, the curvature stress estimate and the finite-time position moment used as inputs each have separate Lean proofs.
