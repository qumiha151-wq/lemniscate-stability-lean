# Complete escape of bending energy to large curvatures in a saturating RMS time window

Use the normalization and notation of the [fourth-moment theorem](CriticalFourthMoment.md). On a fixed interval \([0,T]\) of initial RMS time, suppose \(U_j(0)\to\infty\) and \(\int_0^T\rho_j(t)dt\to0\). For any \(0<T'<T\) and \(a>0\),
\[
 \int_0^{T'}\Big\langle{\bf1}_{\{|k_j|\ge a\}}\Big\rangle dt\to0 .
                                                                    \tag{1}
\]
Here \(\langle\cdot\rangle\) denotes normalized arclength on each slice. In particular, for each fixed \(B<\infty\),
\[
 \int_0^{T'}\big\langle k_j^2{\bf1}_{\{|k_j|\le B\}}\big\rangle dt\to0,
 \qquad
 \int_0^{T'}\big\langle k_j^2{\bf1}_{\{|k_j|> B\}}\big\rangle dt
       \longrightarrow\int_0^{T'}4(16+12t)^{-1/2}\,dt .              \tag{2}
\]
The normalized arclength fraction carrying this bending energy vanishes in spacetime. This excludes persistent saturation with a uniformly integrable squared curvature. It does not rule out concentration on a single evolving curve.

## A local bound at a moving material origin

Work on any forward time interval of length at most \(T\) about a fixed material origin. Let \(s\) be its current signed arclength coordinate, with unit-speed metric and origin \(0\). Assume throughout an upper bound and a positive lower bound for \(\lambda(t)=E/(2L)\). For \(R=F-\lambda k\) set \(r(t)^2=\int_{-4}^4R^2ds\), using a single arclength chart. If initially \(\int_{-4}^4 k^2ds\le C_0\) and \(\int r^2dt=o(1)\) along a sequence of charts, then on these forward intervals
\[
  \int\left(\sup_{|s|\le 3} k^4+\sup_{|s|\le 3} k_s^2\right)dt=O(1).
                                                                    \tag{3}
\]
If initially \(r\) is bounded, the initial pointwise curvature and slope on \([-3,3]\) are bounded as well. All constants are independent of the total curvature and full length.

In the current arclength coordinate the tangential velocity \(\alpha\) satisfies \(\alpha_s=-kF,\ \alpha(t,0)=0\). The actual bending density \(e=k^2/2\) obeys
\[
 e_t=-F^2+\partial_s(k_sR-kR_s+\alpha e).
\]
This is the material bending-flux identity in the unit-speed gauge. The terms containing \(\lambda k\) cancel in \(k_sF-kF_s\). Also \(kF\ge-R^2/(4\lambda)\), so \(\operatorname{sgn}(s)\alpha(t,s)\le r(t)^2/(4\lambda(t))\) for \(|s|\le4\). Define \(b(t)=\int_{\rm start}^t r(v)^2/(4\lambda(v))\,dv\), and choose a smooth nonincreasing \(\psi\) on the nonnegative reals equal to \(1\) on \([0,2]\) and \(0\) on \([3,\infty)\). The cutoff \(\chi(t,s)=\psi(|s|+b(t))\) is smooth at \(s=0\), equals one on \([-1,1]\) for all large indices, and satisfies \(\chi_t-\alpha\chi_s\le0\). Its first two spatial derivatives are bounded independently of \(j,t\).

Write \(m(t)=\int\chi e\,ds\), \(W=(k^2/2-\lambda)T+k_sN\), \(Y=\sup_{[-4,4]}|W|\). Since \(W_s=RN\), its oscillation on this interval is at most \(\sqrt8\,r\). Select a fixed nonnegative smooth \(\phi\) supported in \((-1,1)\) with integral one. Twice integrating by parts gives
\[
 \int\phi |W|^2ds
 =\int\phi(3k^4/4-2\lambda k^2+\lambda^2-kR)\,ds
      +\tfrac12\int\phi'' k^2\,ds .
\]
The left side is at least \((Y-\sqrt8\,r)_+^2\). On the right \(\int_{-1}^1 k^2ds\le2m\) and \(k^2\le2(Y+\lambda)\) everywhere. Hence the right side is at most \(C[1+(1+Y)m+\sqrt{m}\,r]\). By separating \(Y\le2\sqrt8\,r\) and using Young's inequality in the complementary case,
\[
 Y\le C(1+m+r),\qquad \sup |k_s|+\sup k^2\le C(1+m+r).           \tag{4}
\]
The constants in (4) are uniform at all times, even when \(r(t)\) is large.

Integrating the bending-density identity against \(\chi\) gives
\[
 m'=-\int\chi F^2\,ds+\int(\chi_t-\alpha\chi_s)e\,ds
           -\int(\chi_{ss}k+2\chi_s k_s)R\,ds
     \le C[(1+m)r+r^2],
\]
where (4) controls the last integral. As \(m\) is initially bounded and \(\int(r+r^2)dt\) is bounded, Grönwall gives a uniform upper bound for \(m\). Now (4) squared and time integrated gives (3). The initial pointwise assertion follows from (4) at the initial slice.

## From positive arclength fraction to a forbidden patch

From the exact energy and length variations, \(\lambda_j\to(16+12t)^{-1/2}\) uniformly, the lengths are comparable throughout to \(P_j=L_j(0)\to\infty\), and \(\int_0^T\langle R_j^2\rangle dt\to0\). Details are in the [fourth-moment proof](CriticalFourthMoment.md). If (1) failed, a subsequence would admit fixed \(d,d'>0\) and sets of starting times in \([0,T']\), of time measure at least \(d'\), at which the arclength fraction with \(|k|\ge a\) is at least \(d\). Choose one starting time \(t_j\) from each set with \(\langle R^2(t_j)\rangle=o(1)\). After another extraction \(t_j\) converges. Use any fixed forward duration \(0<\ell<T-T'\).

Use arclength at \(t_j\) for the initial sampling measure on material labels. The set where the arclength density relative to that initial measure ever falls below \(1/2\) has initial fraction \(o(1)\), by \(g_t=kFg\ge-R^2g/(4\lambda)\). On its complement the initial sampling measure is dominated by twice the running arclength. Thus, averaged over these labels, each local integral of \(R^2\) over \(|s|\le4\) and the forward time interval has size \(o(1)\) by spatial Fubini. The initial local \(R^2\) integral also has mean \(o(1)\). The initial local \(k^2\) integral has bounded mean since \(\langle k^2\rangle=4\lambda\). Select a label from the fraction \(d\) with \(|k|\ge a\), bounded initial local \(k^2\), bounded initial local \(R^2\), and \(\int_{t_j}^{t_j+\ell}r^2dt=o(1)\). Markov's inequality with a sufficiently large fixed threshold for \(k^2\) and a vanishing threshold for the spacetime residual makes all these conditions simultaneous.

By (3) and (4) this origin now has bounded initial local slope, bounded local spacetime fourth curvature moment and squared slope, and vanishing local squared residual. Its initial curvature, of magnitude at least \(a\), retains one sign with magnitude at least \(a/2\) on a fixed small interval. These are exactly the local hypotheses used in the spacetime compactness and compatibility argument of the [fourth-moment proof](CriticalFourthMoment.md). One may switch to \(x=s/h_j(t)\), \(h_j=L_j(t)/L_j(t_j)\), on a fixed smaller window inside \(|s|<3\); uniform upper and lower bounds on \(h_j\) preserve all stated local bounds. That argument yields a nonzero smooth patch satisfying both \(F=\lambda_* k\) and the incompatible laws \(\lambda_*'=-4\lambda_*^3,\ \lambda_*'=-6\lambda_*^3\). This proves (1).

For (2), split the truncated square at \(a>0\). Its time integral is bounded by \(T'a^2+B^2\int_0^{T'}\langle{\bf1}_{\{|k|\ge a\}}\rangle dt\). First take the limit in \(j\), then \(a\downarrow0\). The full mean square equals \(4\lambda_j\), giving the remaining assertion. Hölder or Cauchy–Schwarz also shows directly from (1)–(2) that the time integral of \(\langle |k|^p\rangle\) must diverge on every positive interior time interval for **every \(p>2\)**.

## Two simultaneous bounds on total absolute curvature

Let \(\mathcal A=\int |k|\,ds\). At a time chosen uniformly from any fixed positive-length interior subinterval, in probability along the sequence,
\[
             \frac{\mathcal A}{U^{1/3}}\longrightarrow+\infty,
       \qquad \frac{\mathcal A}{U^{1/2}}\longrightarrow0 .              \tag{5}
\]
For the second limit, (1), the bounded spacetime mean of \(k^2\) and Cauchy–Schwarz give \(\int\langle |k|\rangle dt\to0\). Since \(L/\sqrt U=\sqrt{L/E}\) is bounded in the initial RMS units, Markov's inequality gives the claim.

For the first limit, the scalar physical identities give \((\log U)'=4\lambda^2(1/2-\rho)\); therefore \(U/U(0)\) stays bounded above and away from zero throughout. Also \(\rho\to0\) in time measure. On any sequence of slices with \(\rho\to0\) the products go to infinity and \(U'\ge0\) eventually. The [increasing-record stress profile estimate](RecordStressProfiles.md) then gives \(U^{1/3}\max|k|/E\to0\). Since \(2E\le(\max|k|)\mathcal A\), the first limit in (5) follows by the sequential criterion for convergence in measure. Explicitly, a set of bad times with positive limiting measure would contain a sequence with \(\rho\to0\), contradicting that slice estimate.

For a single flow with \(L(t)\sim\ell t^{1/3}\) and \(E(t)\sim(\ell/\sqrt3)t^{-1/6}\), the proof of (2) in the [fourth-moment note](CriticalFourthMoment.md) shows that these conclusions hold on every fixed-ratio physical time window after initial RMS dilation. Thus for each fixed multiplier the bending energy of such windows must come asymptotically entirely from curvatures above that multiplier times the initial RMS curvature. On these windows \(U\asymp t^{1/6}\), so the two bounds (5) read \(\mathcal A/t^{1/18}\to+\infty\), \(\mathcal A/t^{1/12}\to0\) in time measure normalized by the window length. The selection, localization and compactness arguments above are written proofs. They have not been checked in Lean.
