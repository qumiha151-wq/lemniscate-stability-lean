# Enclosing radii and length growth in the free elastic flow

For every smooth closed immersed plane free elastic flow the radius \(R(t)\) of its smallest enclosing disk satisfies
\[
                 \limsup_{t\to\infty} R(t)^4/t\ \ge 2 .
\]
The center may be chosen independently on every slice. The expanding round circle has \(R(t)^4=R(0)^4+2t\) and attains the constant. The statement applies to curves of all turning numbers, including immersed curves with self-intersections. The general upper bound for length is a separate open question.

## The enclosing disk

For a fixed center \(z\), write \(p=(X-z)\cdot N\). Integrating the derivative of \((X-z)\cdot T\) gives \(\int kp=-L\). The dilation virial is \(\int Fp=-E\). If the image lies in a disk of radius \(r\) centered at \(z\), then \(\int p^2\le Lr^2\), so Cauchy–Schwarz gives \(L\le 2Er^2\) and \(E^2\le DLr^2\). Combining with \(EL\ge 2\pi^2\) gives
\[
             E\le 2D r^4,\qquad Er\ge\pi .
\]
The inequalities pass continuously to the infimum \(R\) over containing radii. The enclosing radius changes by at most the Hausdorff distance between two compact images, so it is continuous in time. In particular, if \(E\) has positive limit, then \(\int_T^\infty R(t)^{-4}dt<\infty\) by the energy identity.

If \(R(t)^4\le Ct\) on a tail with \(0<C<2\), integrating \((\log E)'=-D/E\le-1/(2Ct)\) gives \(E(t)\le C_1t^{-1/(2C)}\). The lower estimate \(ER\ge1\) gives \(E(t)\ge (Ct)^{-1/4}\), a contradiction. The Lean proof uses the same bounds and integrates the derivative of \(t E^4+(2-C)C^{-2}\log t\). It proves the existence of times beyond every prescribed \(T\) at which \(R(t)^4>Ct\), allowing an infinite limsup. Circle sharpness follows from the explicit radius law, since a disk containing two antipodal points must have radius at least half their distance. [Disk and virial estimates](../../LengthGrowth/ActualFlow/EnclosingDisk.lean) · [Actual radius theorem](../../LengthGrowth/ActualFlow/RadiusGrowth.lean) · [Exact circle evolution](../../LengthGrowth/ActualFlow/SharpCircle.lean)

## Type-I hypothesis on the root-mean-square curvature

Let a smooth closed immersed plane curve evolve by the normal free elastic flow, with force \(F=k_{ss}+k^3/2\), length \(L\), energy \(E=\tfrac12\int k^2\,ds\), and dissipation \(D=\int F^2\,ds\). Suppose \(\sqrt t\,E(t)\le rL(t)\) for all \(t\ge T>0\), where \(r>0\). Equivalently, \(t^{1/4}\) times the root-mean-square curvature is at most \(\sqrt{2r}\). Put
\[
a=r\sqrt{1+r^2}-r^2,\qquad a^2=r^2(1-2a),\qquad 0<a<1/2.
\]
Then \(L(t)=O(t^a)\) and \(E(t)=O(t^{a-1/2})\). In particular the critical tail bound \(8tE^2\le L^2\) gives \(L(t)=O(t^{1/4})\). Under this same critical bound the normalized curves converge smoothly, up to reparametrization, to a possibly multiply covered circle. The estimates for general \(r\) and the critical fourth-root bound are formalized in Lean. The circular convergence is an analytic result.

## Differential estimate

The material first variations give \(E'=-D\), \(L'=\int kF\,ds\), and \((L')^2\le 2ED\). For \(H_a=aL^2+tE^2\), completing the square gives
\[
2aH_a-tH_a'=
(tL'-aL)^2+t^2\big(2ED-(L')^2\big)
+a^2L^2-(1-2a)tE^2 .
\]
The tail hypothesis makes the right side nonnegative. Thus \(H_a/t^{2a}\) is nonincreasing. Bounding \(aL^2\le H_a\) proves the length estimate, and the assumed bound on \(E/L\) gives the energy estimate. The exponent is attained in the scalar differential inequalities by \(L=t^a,\ E=r t^{a-1/2}\). These scalar functions alone do not construct a geometric flow. An expanding round circle realizes the critical asymptotic ratio \(r=1/\sqrt8\). [Weighted derivative and monotonicity](../../LengthGrowth/ActualFlow/RMSTypeI.lean) · [Actual length and energy estimates](../../LengthGrowth/ActualFlow/RMSPowerGrowth.lean)

## Compactness and rigidity at the critical bound

Set \(a=1/4\). Write \(H=H_{1/4}\), and call the three nonnegative terms above \(Q_1,Q_2,Q_3\) in order. Since \(-(H/\sqrt t)'=(Q_1+Q_2+Q_3)/t^{3/2}\), the integral from \(T\) to infinity is finite. The boundedness of \(H/\sqrt t\) bounds both \(t^{-1/4}L\) and \(t^{1/4}E\) above. Their product is at least \(2\pi^2\) by total absolute turning and Cauchy–Schwarz, so both are bounded below by positive constants.

For \(t_j\to\infty\) take the parabolic dilations \(X_j(u)=t_j^{-1/4}X(t_j u)\) on \(1/4\le u\le 3\). Length, energy and total dissipation on these slabs are uniformly bounded, and length has a positive lower bound. The three \(Q_i\) for the dilated flow equal \(t_j^{-1/2}Q_i(t_j u)\). Their weighted integrals on the slabs are the original tail integrals and tend to zero.

Here the spatial parameter circle stays compact in the limit. For the interior estimates put \(Q(u)=\max_{0\le i\le3}\|\partial_s^i k\|_\infty^{1/(1+i)}\). If \(Q\) is arbitrarily large on \(1/2\le u\le5/2\), start at such a time. Whenever the past time interval of duration \(Q^{-4}\) contains a value exceeding \(2Q\), restart there. This terminates by smoothness on a compact time interval. Its total backward displacement, including the final interval, is at most \(16Q_{\rm start}^{-4}/15\). At the selected endpoint let \(q=Q\) and dilate space by \(q\). On one unit past time interval the curvature derivatives through order three are bounded, a terminal derivative has absolute value one, the period tends to infinity, and the total integral of squared curvature is \(O(q^{-1})\). The uniform spatial Lipschitz bound then gives uniformly vanishing curvature. Interpolation with the third derivative gives vanishing first and second spatial derivatives as well.

On the arclength chart of radius two anchored at the selected material point, the tangential speed satisfies \(\xi_s=-kF,\ \xi(0)=0\). The curvature equation has leading term \(-\partial_s^4k\) and source \(-5k^2k_{ss}/2-3kk_s^2-k^5/2+\xi k_s\). This source tends uniformly to zero. With a cutoff equal to one near the terminal point, the biharmonic heat kernel gives vanishing third derivative there too: its third derivative has spatial \(L^1\) norm \(O(\tau^{-3/4})\) at time distance \(\tau\). The cutoff commutators can be integrated by parts to leave the undifferentiated curvature multiplied by off-diagonal kernel derivatives, which are integrable at time zero. This contradicts the unit terminal derivative. For higher orders on the original slabs, bounded derivatives through order \(m\ge3\) bound the source derivatives through order \(m-2\) on arclength charts of any sufficiently small fixed radius. The same kernel argument with \(m-2\) derivatives moved onto the source bounds the order \(m+1\) derivative in the interior. Iteration gives every spatial derivative on \(1\le u\le2\).

At \(u=1\) choose normalized arclength as material coordinate on the unit parameter circle, and translate the base point to zero. The metric density \(g=|X_x|\) initially equals the entire length. The identity \((\log g)_u=kF\) bounds \(g\) above and away from zero through \(u=2\). Differentiating this identity in the material coordinate, with \(\partial_x=g\partial_s\), bounds successive spatial derivatives of \(g\) inductively. The velocity \(-FN\) bounds position displacement, and the Frenet and evolution equations then control all space and time derivatives. A subsequence converges smoothly on interior subslabs to a closed immersed solution of the same physical equation. This argument retains the total curvature integrals, including all multiplicities.

The vanishing of all three integrated nonnegative defects, followed by smooth convergence, gives on every interior limiting slice
\[
uL'=L/4,\qquad \sqrt u\,E=L/\sqrt8,\qquad
F=\lambda k,\quad\lambda=L'/(2E)=1/\sqrt{8u}.
\]
The last identity uses equality in the actual spatial Cauchy–Schwarz inequality. It holds over a time interval. For any such solution, \(k_{ss}=\lambda k-k^3/2\), hence \(k_s^2=\lambda k^2-k^4/4+C(u)\) on each slice. In normal gauge \(k_u=-\lambda^2 k-\lambda k^3/2\), and \([\partial_u,\partial_s]=-\lambda k^2\partial_s\). Differentiating the equation for \(k_{ss}\) in time, commuting the two arclength derivatives, and substituting the first integral gives at \(k\ne0\)
\[
\tfrac94 k^4-9\lambda k^2-5C(u)-\lambda'/\lambda=0 .
\]
At fixed time the possible curvature values belong to the finite set of real roots of this polynomial together with zero. Continuity on the connected parameter circle makes \(k\) constant. A regular closed curve of constant curvature is a circle of nonzero winding, possibly covered several times.

At an interior time of the convergent slabs the normalized curvature oscillation of the original slices therefore tends to zero. One such late slice enters the stability basin of the circle having its turning number. Reverse orientation if needed, and dilate this slice to length \(2\pi |n|\). The normalized time extends to infinity by \(L(t)=O(t^{1/4})\). The small-oscillation convergence theorem then gives circular convergence of the entire length-normalized tail. Smooth convergence also follows from its curvature oscillation convergence and the uniform higher derivative bounds on the above parabolic slabs, since lengths in these coordinates are bounded above and below. The unrestricted length problem would require control of \(\sqrt t\,E/L\) or another argument. [Andrews and Wheeler, Theorems 1 and 2](https://arxiv.org/html/2509.11129v2)
