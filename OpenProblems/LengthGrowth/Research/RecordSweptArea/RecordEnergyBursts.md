# Short physical-time energy drops at high trigonometric records

Consider one smooth closed free elastic flow. Put \(E=\frac12\int k^2ds\), \(L=\int ds\), \(U=EL\), \(D=\int F^2ds\), \(F=k_{ss}+k^3/2\) and \(m_t^2=2E(t)/L(t)\). Suppose \(t_j\to\infty\) are successively higher global product records with \(U_j=U(t_j)\to\infty\). Assume that at these individual times

* \(W(X(t_j))/L(t_j)^2\ge a>0\), with \(W=\int |\operatorname{wind}|\,dz\). The same proof works for the matrix transport quantity \(J\) in [TreeLikeRecordLimits.md](TreeLikeRecordLimits.md).
* \(D(t_j)/(m_j^4 E(t_j))\ge b>0\), with \(m_j=m_{t_j}\).

Then
\[
       -\frac{t_j E'(t_j)}{E(t_j)}
       =\frac{t_jD(t_j)}{E(t_j)}\ \ge\ c(a)b\,U_j.                         \tag{1}
\]
If, in addition, after dilation by \(m_j\) the unit tangents have uniformly bounded spatial derivatives through order eight in arclength at the individual record times, there are \(\delta,\eta>0\), independent of \(j\), such that
\[
 E(t_j+\delta m_j^{-4})\le(1-\eta)\,E(t_j),
 \qquad \delta m_j^{-4}/t_j\longrightarrow0.                               \tag{2}
\]
In particular no flow whose energy is regularly varying at infinity with finite index can have this record behavior. Neither conclusion assumes a positive limiting energy.

## Applying the conditions to the outward representatives

Fix any signed turning number, including zero. For the high prescribed-level trigonometric representatives, the first hypothesis holds by their uniform macroscopic position limit. It persists under a vanishing positional perturbation in units of total length. For the second, let \(w=k/A,\ h=F/A^3\) in the unit-speed parameter of the representatives, and use the angular mean there. Then \(D/(m^4 E)=2\langle h^2\rangle/\langle w^2\rangle^3\). This number is at least \(1/8\) even if \(w,h\) are uniformly within \(1/1000\) of the fast profiles \(f(Ns),H(Ns)\), respectively. Indeed the means of the reference squares are \(4097/2048\) and \(60523245573/68719476736\). Their supremum norms are at most \(3\) and \(17\). A uniform perturbation of size \(\varepsilon\) changes the squared mean by at most \(\varepsilon(2\|f\|_\infty+\varepsilon)\) for the first profile, and the corresponding expression with \(H\) for the second. This gives \(0<\langle w^2\rangle\le21/10\), \(\langle h^2\rangle\ge4/5\), and hence the asserted lower bound. The exact representatives satisfy the two perturbation bounds. [Prescribed outward levels and their normalized force](../MulticoverBarrier/PrescribedTrigonometricLevels.md)

Their normalized derivatives of every fixed order are uniformly bounded for each fixed turning number. In the coordinate dilated by \(m=A\sqrt{\langle w^2\rangle}\), the fast spatial frequency is \(N/m=O(1)\), the small slow terms have bounded coefficients, and the Frenet equations transfer those bounds to the tangent. Thus (2) also applies to strong approximations that retain the uniform order-eight bound. Positional approximation alone imposes no force or derivative bound.

Choose \(q>1\) so large that \(d=a-1/(4\pi q^2)>0\). At every sufficiently large record \(t\) the length passes from \(L(t)/q\) at some \(s\ge0\) to \(L(t)\). The swept-area estimate gives \(m_t^4(t-s)\ge4d^2 U(t)/(q-1)\). Multiplying by \(D(t)/(m_t^4E(t))\) proves (1) with \(c(a)=4d^2/(q-1)\). It also gives \(m_j^{-4}/t_j\to0\). [Physical-time record crossing inequality](WindingAreaRecords.md)

## A uniform forward interval

Here is the short-time estimate needed for (2). Work after the fixed dilation by \(m_j\) at the initial time of each interval. Its RMS curvature is one, its length is \(P_j\), and its initial energy is \(P_j/2\). Parametrize initially by arclength \(x\), retaining the entire periodic parameter. A tangential reparametrization of normal elastic flow gives an equation for the position \(Y\) of the form
\[
      Y_\tau=-|Y_x|^{-4}Y_{xxxx}+H(Y_x,Y_{xx},Y_{xxx}).
\]
The function \(H\) is smooth where \(Y_x\ne0\). Indeed \(k_{ss}\) has fourth-order term \(|Y_x|^{-4}Y_{xxxx}\cdot N\); retaining the full vector in that term specifies the tangential velocity. Differentiate in \(x\) and set \(V=Y_x\). Then
\[
       V_\tau=-|V|^{-4}V_{xxxx}+G(V,V_x,V_{xx},V_{xxx}),                   \tag{3}
\]
with smooth \(G\) on the same set. Each periodic smooth initial field has a classical solution for short time in this strictly parabolic gauge, and the corresponding normal flow is the same up to parametrization. The following estimate gives a common time for all the periods. [Fourth-order parabolic elastic-flow gauge](https://arxiv.org/abs/1912.09626) · [Parabolic existence and continuation in Hölder spaces](https://www.aimsciences.org/article/doi/10.3934/eect.2020017)

Extend \(V\) periodically to the real line. Let \(\omega_y(x)=\exp(-\sqrt{1+(x-y)^2})\) and
\[
       K_y=\sum_{k=0}^8\int_{\mathbb R}\omega_y|\partial_x^k V|^2dx .
\]
Initially \(K_y\le K_0\) uniformly in \(j,y\), and \(|V|=1\). Stop while \(1/2\le |V|\le2\) and \(\sup_y K_y\le 2K_0+1\). Ordinary one-dimensional Sobolev embedding on the overlapping intervals \([y-1,y+1]\) gives a uniform supremum bound on all derivatives through order seven. On the stopped interval, differentiation in (3) and integration by parts give constants independent of the period and \(y\) such that
\[
       K_y'+c\int\omega_y|\partial_x^{10}V|^2\le C(1+K_y).                 \tag{4}
\]
For detail, in \(\partial_x^8( -|V|^{-4}V_{xxxx})\) the leading term integrates twice into \(-\int\omega_y |V|^{-4}|\partial_x^{10}V|^2\). The terms from the two differentiated weight and coefficient have lower order. The only other terms of order eleven are a smooth bounded coefficient times \(\partial_x^{11}V\), from differentiating the principal coefficient once or the third argument of \(G\) eight times. One integration by parts reduces these to products of \(\partial_x^{10}V\) with derivatives of order at most nine and uniformly bounded coefficients, whose first derivatives are also bounded. In terms of order ten or less, at most one factor has order eight or greater: even for two factors starting at order three this would require at least ten derivative allocations. The derivatives through seven and all coefficient derivatives that occur without higher factors are controlled on the stopped interval. The terms from \(k<8\) are treated by the same integrations or are already lower order. Since \(|\omega'_y|+|\omega''_y|\le C\omega_y\), weighted integration by parts and Young's inequality give \(\int\omega_y|V^{(9)}|^2\le\epsilon\int\omega_y|V^{(10)}|^2+C_\epsilon\int\omega_y|V^{(8)}|^2\). Absorption gives (4).

The right side of (4) stays bounded, so \(K_y\) cannot reach its stopping bound in a sufficiently short common interval. Equation (3) gives \(\|\partial_\tau V\|_{C^3}\le C\) there, since it uses at most seven spatial derivatives. Hence \(\|V(\tau)-V(0)\|_{C^3}\le C\tau\), and the speed cannot reach either stopping value in a shorter fixed interval. On each individual circle the bounds keep (3) uniformly parabolic with bounded \(C^{4+\alpha}\) data for any fixed \(0<\alpha<1\); the classical continuation criterion therefore extends the gauge through that interval if needed. This proves the uniform estimate, without a restriction on the growing initial period.

The geometric force is a smooth function of \(V,V_x,V_{xx},V_{xxx}\) as long as \(|V|>0\). Thus \(\|F(\tau)-F(0)\|_\infty\le C\tau\) in these coordinates. At \(\tau=0\) the unweighted spatial mean of \(F^2\) is at least \(b/2\), since \(E(0)=P_j/2\) in these units. On a fixed interval \([0,\delta]\), the \(L^2(dx/P_j)\) norm of \(F\) remains at least \(\tfrac12\sqrt{b/2}\) and the speed remains at least \(1/2\). It follows that \(D(\tau)\ge P_j b/16\) throughout. Integration gives (2) with \(\eta=b\delta/8\), shortening the interval to ensure \(0<\eta<1\).

For an eventually regularly varying nonincreasing energy, \(E((1+h_j)t_j)/E(t_j)\to1\) whenever \(h_j\downarrow0\), or more generally \(h_j\ge0,\ h_j\to0\). This follows by comparison with \(E((1+h)t_j)/E(t_j)\) for each fixed \(h>0\), then letting \(h\downarrow0\). It contradicts (2).

Lean checks the uniform moment bound, the passage from physical swept area and terminal force to (1), integration of a dissipation floor on the actual energy, and the vanishing of relative losses on short windows for regularly varying energies. The local parabolic estimate that supplies the floor in (2) is a written proof. They give necessary behavior for a putative trajectory shadowing the prescribed high-level states. A general trajectory may have different record profiles or undergo the indicated short energy drops.
