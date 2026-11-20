# Independent check of the matching argument

The following checks concern the physical arclength equation
\(k_{ss}+k^3/2=-(X-O)\cdot N\) at dilation coefficient one, the two frozen tail enclosures, and the incoming and matching estimates in the companion notes.

## Scaling and signs

With \(O=0\), \(R=|X|\), \(\theta=\arg T-\arg X\), one has \(R_s=\cos\theta\), \((\arg X)_s=\sin\theta/R\), and \(X\cdot N=-R\sin\theta\). Differentiating \(k/R^{1/3}, k_s/R^{2/3}, R^{-4/3}\) in \(d\sigma=R^{1/3}ds\) gives precisely the four inner equations, including the signs of the \(\sin\theta\) terms. The incoming radial coordinate and the impact, in the notation of RealIncomingLayer.md, are \(A\delta^{-2/3}r^{-2/3}\,\eta/r\) and \(I\delta^{-1/3}r^{-4/3}\). Thus the finite radial coordinate is matched at the same physical radius. Rotating the entire state to put the radial vector along the vertical loses only the global rigid rotation.

For frozen vertical forcing and a horizontal seam tangent, \(K,p,B,A\) are even and \(V,q,H\) are odd about the seam. Thus the transverse impact \(B/\sqrt A\) is identical on the two reflected ends of a given seam. The opposite signs for the two seam *parameters* persist on their incoming ends. In particular there is no sign reversal between the two frozen certificates when they are used at the incoming section.

The derivative calculation for the corrected impact reduces to
\[
 -U\Psi_\phi/2+u(\zeta\Psi_\eta-\eta\Psi_\zeta)-w\Psi
 =U[-uw(\eta^2/3+\zeta^2/12)+(u^2/2+3w^2/4)\eta\zeta].
\]
The absolute bound for its product with \(p\) is at most
\(\sqrt2(1/6+3/8)<0.77\). Under \(A\ge11,\ |I|\le0.4\) it is at most
\(\sqrt2(1/6+3(0.4)/(4\sqrt{11}))<0.37\).
The stated \(1.66A^{-3/2}\) errors in the corrected radial derivative give the \(0.28\) and \(0.61\) forward growth bounds used to integrate the respective remainders.

Both integrations were independently rerun with the stored Python/Arb checker at its stated 512-bit precision, 2,048 steps per orbit, and order 38. Every output field agreed with the two stored JSON records. The corrected impacts at arclength 20 were enclosed by \(-0.09848108914527997945321050\pm4.12\cdot10^{-27}\) and \(0.9021025263281717045061802\pm2.34\cdot10^{-26}\). The differential inequality after arclength 20 then proves the strict signs at arbitrarily far incoming sections.

## Uniformity, entry and matching

Uniform boundedness of all the frozen impacts on arbitrarily high sections follows before choosing the section level. All seam orbits satisfy \(h'=p^2\ge0,\ h\to\infty\) on the outgoing end. The compact seam interval, finite-time continuous dependence and monotonicity give one time \(t_0\) at which \(h>11\) for all seam parameters. All states are bounded there. On the remainder of every tail the same estimate
\(\int_{t_0}^\infty A^{-2}ds\le[0.28(11-2\cdot0.143)]^{-1}\) applies. The corrected impact and then the actual impact are uniformly bounded. Reflection transfers this bound to all incoming ends, so the chart threshold can be chosen before constructing the matching rectangle.

For the physical outer shot the extra term in the derivative of
\(I=(W\wedge Z)/\sqrt A\) comes from \(W\wedge Z_\tau=-Aw\).
The given primitives \(P,Q\) differentiate to the required zero-mean phase variations. Subtracting their corrections cancels the leading derivative of phase and costs \(O(\delta/A^2)\), \(O(\delta/A^{3/2})\), respectively. Monotonicity of \(A_c\) before the stopping event justifies integration in \(A_c\), without assuming that \(A\) itself decreases. Thus the fixed high incoming section has \(|\mathcal I|=O_a(\delta^{2/3})+O(1/H)\), while the lifted phase diverges. Take \(H\) large before taking \(b=1/\delta\) large. Compactness and transversality give a single high incoming crossing on the late segment, and its preceding phase never needs to be continued through \(W=0\).

When perturbing the seam by its radius variable, \(\partial\epsilon_{\rm in}/\partial\epsilon_s=1\) at \(\epsilon_s=0\) because its differential equation starts at quadratic order. The implicit selection of \(\epsilon_s\) is uniform on the compact seam interval. At fixed active section height the leading radial coordinate \(\sqrt{A(A-I^2)}\) is strictly increasing with derivative at least one and dominates the \(O(A^{-3/2})\) derivative correction. The phase and the signed impact therefore recover the full inner state on the incoming branch. The two pairs of strict opposite face signs in the matching rectangle imply a common zero by coordinatewise clipping and Brouwer. Its forward flight to the true seam has positive length by persistence of the frozen, strictly positive flight over this compact family.

## Physical closure and distinct shapes

Write \(p=(X-O)\cdot N,\ q=(X-O)\cdot T\). The two reversors are
\(R_0(k,v,p,q)=(-k,v,-p,-q)\) and \(R_1(k,v,p,q)=(k,-v,p,-q)\). If the centre at time zero and seam at \(s_*>0\) are fixed by the corresponding reversors, then \(Y(s+2s_*)=R_1R_0Y(s)=(-k,-v,-p,q)(s)\). Curvature has zero integral over \(4s_*\). The tangent and normal return after that interval, as do \(p,q\), giving closure through \(X-O=qT+pN\). The minimum support period may divide \(4s_*\); existence of the underlying primitive closed immersion follows from regularity and its analytic periodic position parametrization.

For distinction under arbitrary similarities, if two coefficient-one profiles differ by a scale \(d\), rigid motion and possible reversal, writing the dilation equations on the same physical immersion shows \(((1-d^{-4})X+C)\cdot N=0\) with a fixed vector \(C\). If \(d\ne1\), this would give \((X-P)\cdot N=0\) everywhere. At a maximum of \(|X-P|>0\) the vector \(X-P\) is normal to the curve, a contradiction. With \(d=1\), the centre is unique since a constant vector tangent to every point of a regular closed curve must vanish. The already proved centre-marker rigidity for reflected orbits implies that every zero-curvature passage through this centre has \(|k_s|=b\), unchanged by reversing the curve or taking a cover. In particular different successful \(b\)'s produce different primitive shapes. The weaker observation that \(|k_s|\) is bounded on every fixed smooth closed shape suffices for infinitude.

## Counting consequence

The same estimates give a linear lower bound for the number of distinct normalized reflected profiles whose centre marker does not exceed \(B\), for all sufficiently large \(B\). Fix the section \(H\) used for matching. On the late incoming segment \(A\le C a\), its slow duration is at most \(Ca\), and \(\delta\phi_\tau\le(1+C/L^{3/2})\sqrt A\). Thus this segment contributes at most \(Ca^{3/2}\) to \(\delta\Phi\). On the preceding fixed slow time segment the outer averaging estimate gives the corresponding integral of \(\sqrt{1-\tau^2/\tau_*^2}\) in the limit. Sending \(a\) to zero now yields
\[
        \lim_{b\to\infty}\Phi(b)/b = \pi\tau_*/4 .
\]
Fix a lower marker \(b_0\) with strict endpoint impact margins, and let \(D\) be the oscillation of the seam phase lift on its compact parameter rectangle. All integers \(n\) strictly between \((\Phi(b_0)-\min\Phi_\Gamma)/P\) and \((\Phi(B)-\max\Phi_\Gamma)/P\) have a matching marker in \([b_0,B]\), by the same rectangle argument. Each marker accounts for at most \(1+\lfloor D/P\rfloor\) integers, even if one orbit hits several seams. Consequently there is a constant \(c>0\) such that at least \(cB\) distinct normalized primitive shapes have a marker in this interval for every sufficiently large \(B\).

## Geometry and primitive length of the matched family

For fixed \(H\), compactness bounds the inner flight time from the matched incoming section to the seam in the \(\sigma\) clock. There \(R\) initially has size \(z_*\sqrt b(1+o(1))\). The exact equation \((R^{4/3})_\sigma=4\cos\theta/3\) keeps \(R^{4/3}\) within a bounded additive error throughout the flight, so its physical arclength is \(O(b^{-1/6})\). The outer entry estimate therefore gives \(s_*/\sqrt b\to\tau_*\) for the matched seam.

For any positive match the two reversors give a period \(4s_*\) and a phase translation by \(2s_*\) that changes the sign of the centre derivative \(b\). Let \(P_{\rm sup}\) be the least period of the support orbit; it exists since that orbit is smooth, periodic and nonconstant. The translation by \(2s_*\) has order two on the support phase circle and is nontrivial, hence \(2s_*=P_{\rm sup}/2\pmod{P_{\rm sup}}\). Thus \(s_*\) is an odd multiple of \(P_{\rm sup}/4\), and \(P_{\rm sup}/4\) is itself a seam: its phase differs from \(s_*\) by a multiple of \(P_{\rm sup}/2\), and the half-period sign change preserves \(v=q=0\). If the odd multiple exceeded one, there would be a positive seam by \(s_*/3\). The outer fixed-time proof excludes every seam before \((\tau_*-o(1))\sqrt b\). This rules out a multiple exceeding one on any sequence of successful markers tending to infinity. The reconstructed position closes after \(4s_*\), and any position period is a support period, so the primitive position length is \(4s_*\) for all sufficiently large successful markers. In particular the primitive length divided by \(\sqrt b\) tends to \(4\tau_*\).

The maximum of \(|X|/\sqrt b\) on the first quarter tends to \(z_*=\gamma\tau_*\): fixed outer times give the radii \(\gamma\tau+o(1)\), the late incoming time window has length \(O(a)\) in slow time during which \(|Z_\tau|=1\), and the final inner flight has physical length \(O(b^{-1/6})\). Both reversors preserve \(p^2+q^2=|X|^2\), so the same asymptotic holds for the maximum radius of the complete primitive profile.

Let \(N(b)\) be the number of sign-changing zeros of curvature around the primitive immersion. The same argument gives
\[
 \lim_{b\to\infty}\frac{N(b)}{b}=\frac{2\pi\tau_*}{P}.
\]
On the centre-to-section portion the phase is strictly increasing, with exactly two simple zeros per full period, so the quarter count to the section is \(2\Phi(b)/P+O(1)\). The number of additional zeros from section to seam is uniformly bounded. To see this, fix a common backward inner-clock interval covering the compact frozen seam family's flights and continue the entire small-parameter family on this interval by smooth dependence. Each trajectory solves a real analytic ODE. Its inner curvature function is analytic in that clock and cannot vanish identically: at the seam it is nonzero unless \(c=0\), in which case \(K=V=0\), \(\theta=-\pi/2\), and the inner equations give \(K_{\sigma\sigma}=-1\). At every point of the compact parameter-time rectangle some finite-order inner-clock derivative of \(K\) is nonzero. On a product neighborhood that derivative stays nonzero. Finitely many such boxes cover the rectangle, and Rolle's theorem bounds the number of distinct curvature zeros in each box on each individual trajectory by its derivative order. Summing gives a uniform bound, which applies whether or not such zeros change sign. Finally four reflected quarters duplicate the interior zeros, with only bounded corrections at their endpoints. This also gives the displayed limit for the number of all distinct material zeros on the primitive parameter circle.

The constant simplifies to \(\sqrt{3\pi/2}\). Integrating one oscillator quarter with \(x=U/\sqrt2\) gives \(P=\sqrt2\,\mathrm B(1/4,1/2)\), and the mean of \(U^2/2\) is \(\gamma=\mathrm B(3/4,1/2)/\mathrm B(1/4,1/2)\). The product of these two beta functions is \(4\pi\) by \(\Gamma(5/4)=\Gamma(1/4)/4\). Thus \(\gamma P^2=8\pi\). Together with \(EL/b^2\to32\) from the main profile proof this yields \(N(b)^2/(EL)\to3\pi/64\).
