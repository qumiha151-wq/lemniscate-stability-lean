# Relative angular velocity at curvature zeros and exact fourth-root growth

Consider a single smooth forward free elastic flow of closed regular plane immersions, using any fixed material parameter circle and the normal gauge \(X_t=-F N\), \(F=k_{ss}+k^3/2\). Here \(s\) denotes instantaneous arclength. On each positive-time slice set
\[
  Z(t)=\{u:k(t,u)=0\},\qquad B(t)=\tfrac12
    \bigl(\max_{Z(t)}F_s-\min_{Z(t)}F_s\bigr).
\]
Set \(B=0\) for an empty zero set. A singleton automatically gives zero. All curvature zeros enter this definition, including touching zeros and entire zero intervals. At each such point \(F_s=k_{sss}\).

**Theorem.** If \(\int_T^\infty B(t)\,dt<\infty\) for some \(T>0\), then \(L(t)=O((1+t)^{1/4})\). More precisely, let \(m_\delta(t)\) be the maximum number of subarcs with disjoint interiors, each having absolute net turning at least \(\delta>0\) on that slice. For \(T\le s<t\) and
\[
                  0<\delta'<\delta-2\!\int_s^t B(r)\,dr
\]
one has \(m_\delta(t)\le m_{\delta'}(s)\), also when the roles of the two times are reversed. In particular, if \(m_{1/4}(t)>m_{1/8}(s)\), then \(\int_s^t B(r)\,dr\ge1/16\). The integral compares the instantaneous angular velocities at zeros at the *same* time and is independent of rotation or of a choice of parametrization.

## Removing a common rotation and a tangential speed

In normal gauge \(T_t=-F_sN\) for the unit tangent. Relabelling points at tangential arclength speed \(\lambda\) adds \(\lambda kN\). A rotation adds a term \(\omega N\). On each slice the infimum of \(\|F_s-\lambda k-\omega\|_\infty\), over smooth periodic \(\lambda\) and real \(\omega\), is \(B\). The zero set gives the lower bound. When the zero set is nonempty, choose \(\omega\) halfway between its extreme values of \(F_s\). Put
\[
               \lambda_\epsilon
                =\frac{k(F_s-\omega)}{k^2+\epsilon^2}.
\]
The error has absolute value \(|F_s-\omega|\epsilon^2/(k^2+\epsilon^2)\). For each \(\eta>0\) the first factor is at most \(B+\eta\) in a neighbourhood of the compact zero set. On its compact complement the error tends uniformly to zero. When the zero set is empty one may take \(\lambda=F_s/k\). This proves the infimum formula without dividing by zero.

On each compact positive-time interval \(B\) is bounded and upper semicontinuous. For a sequence of times with nonempty zero sets, extremizing material labels have convergent subsequences, whose limits are zeros of the limiting slice. At a time with no zeros a whole neighbourhood has no zeros. These observations also cover the creation or disappearance of zeros. On a compact time interval choose a continuous majorant \(g>B\) whose integral differs from that of \(B\) by arbitrarily little. For example approximate bounded upper semicontinuous \(B\) from above by the continuous Lipschitz envelopes \(\sup_r(B(r)-j|t-r|)\), then add a small positive constant and use dominated convergence.

At each time fix \(\epsilon,\omega\) as above giving error strictly below \(g\). The same constants in the displayed smooth formula give this bound on a time neighbourhood. In the zero-free case the quotient is smooth on a neighbourhood. A partition of unity on the time interval gives smooth \(\lambda,\omega\) valid throughout: the error for the convex combination is bounded by the convex combination of errors. This construction works on every compact comparison interval, with an arbitrarily small excess in the integral of the error.

The parameter vector field \(\lambda/|X_u|\) generates increasing diffeomorphisms of the parameter circle for the duration of that interval. Rotate the relabelled tangents at angular speed \(\omega\). A continuous angle lift on the universal parameter cover then has time derivative \(-F_s+\lambda k+\omega\), composed with the diffeomorphism. A uniform change in this angle lift of at most \(A\) changes the net angle on each material subarc by at most \(2A\). Rotation changes both endpoint angles equally. Thus every \(\delta\)-excursion at the terminal time supplies a \(\delta'\)-excursion at the initial time for \(\delta'<\delta-2\int_s^t B\), by choosing the excess sufficiently small. The diffeomorphism preserves disjoint interiors. The same control transports arcs in the reverse direction. Each count is finite because its total angular cost is at most \(\int |k|\,ds\).

Under the finite-integral hypothesis choose \(s\) so late that \(\int_s^\infty B<1/16\). The comparison now gives \(m_{1/4}(t)\le m_{1/8}(s)\) for all \(t\ge s\). The geometric record theorem in the LengthGrowth project implies the asserted exact length bound. Conversely, any failure produces a sequence of increasing-product records on the same trajectory with \(m_{1/4}\to\infty\). From any starting time one can choose successively later records with \(m_{1/4}(t_{j+1})>m_{1/8}(t_j)\), so each intervening interval incurs at least \(1/16\) of the integral of \(B\). [Macroscopic turning at increasing records](MacroscopicTurningAndQuarterGrowth.md)

For an exact rotating or dilating similarity profile the support identities give \(F_s=k(aq-\omega p)-\omega\) at each fixed time in its similarity coordinates. Thus all its curvature zeros have the same \(F_s\) and \(B=0\). For unrestricted flows the integrability of the inflection angular velocity difference remains unproved. The instantaneous minimization, time comparison, and this integral criterion are analytic proofs. Their length-growth implication uses the independently kernel-checked material record theorem.
