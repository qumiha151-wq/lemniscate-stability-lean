# Closing a reflected orbit by matching at the incoming section

Use physical arclength \(s\), dilation coefficient one, and the pure expander equation \(k''+k^3/2=-X\cdot N\), \(N=JT\). Shoot from \(X=0,\ k=0,\ k'=b>0\), fixing the initial tangent. This argument describes the exact finite-dimensional matching step, including the variable physical radius. The outer approximation and two strict frozen impact signs are separate inputs to this step.

## Coordinates in the layer

At \(R=|X|>0\) let \(e=X/R\), and measure the tangent angle \(\theta\) from \(e\). Define \(K=k/R^{1/3}\), \(V=k'/R^{2/3}\), \(\epsilon=R^{-4/3}\) and \(d\sigma=R^{1/3}\,ds\). Then
\[
 \dot K=V-\epsilon K\cos\theta/3,\qquad
 \dot V=-K^3/2+\sin\theta-2\epsilon V\cos\theta/3,\qquad
 \dot\theta=K-\epsilon\sin\theta,\qquad
 \dot\epsilon=-4\epsilon^2\cos\theta/3.
\]
Dots denote \(\sigma\)-derivatives. This follows from \(R_s=\cos\theta\), \(\arg(e)_s=\sin\theta/R\), and \(X\cdot N=-R\sin\theta\). The genuine seam consists of \(V=\cos\theta=0\): both the physical curvature derivative and tangential support vanish there. The seam component with \(N\cdot e=1\) corresponds to \(\theta=-\pi/2\). Holding \(e\) vertical rather than horizontal translates the coordinate angle by \(\pi/2\), giving the horizontal tangent used in the frozen initial-value computations.

Use the scaled stress \(W=(K^2/2)T+VN\), \(A=|W|\), \(d=W/A\), \(\eta=d\cdot e\), \(\zeta=(Jd)\cdot e\). Thus the impact coordinate is \(I=(W\wedge e)/\sqrt A=\sqrt A\,\zeta\). Let \(\phi\) be the phase on the quartic oscillator, of period \(P\), so \(K=\sqrt A\,U(\phi)\), \(V=A U'(\phi)\) and \(U(0)=0,U'(0)=1\). Set \(w=U'\) and \(u=U^2/2\). The frame equals \(T=ud-wJd,\ N=wd+uJd\). In the incoming sector \(\eta>0\), take the corrected radial stress
\[
 \widehat H=W\cdot e+\chi/\sqrt A,\qquad
 \chi=Uw(\eta^2-\zeta^2)/3+U^3\eta\zeta/3 .
\]
For the frozen problem \((W\cdot e)^\cdot=-(N\cdot e)^2\) and
\(\partial_\phi\chi=(N\cdot e)^2-(1+\eta^2)/3\) at fixed \(d,e\). This uses \(w^2+u^2=1\) and \((Uw)'=3w^2-2\). Therefore \(\dot{\widehat H}=-(1+\eta^2)/3+O(A^{-3/2})\) for frozen dynamics, and with an additional \(O(\epsilon A)\) on the true section for \(A\ge1\). The latter error follows either directly from the four equations above or from smoothness on any fixed compact section where \(A>0\).

For each sufficiently large fixed \(H\), bounded impacts \(I\), and all phases, the section \(\widehat H=H,\eta>0\) has coordinates \((\phi\bmod P,I,\epsilon)\). Indeed \(\zeta=I/\sqrt A,\eta=\sqrt{1-I^2/A}\). At fixed \(\phi,I\), the leading term \(\sqrt{A(A-I^2)}\) has derivative at least one with respect to \(A\); the derivative of \(\chi/\sqrt A\) is \(O(A^{-3/2})\) uniformly on bounded impact intervals. On that branch \(A/H\to1\) as \(H\to\infty\). The frame recovers \(T\) uniquely from the stress direction and the oscillator phase in the radial coordinates. Thus matching all three section coordinates suffices, including for finite physical \(b\).

## The seam family survives the return to varying radius

At the frozen seam take \(K=c,\ V=0,\ \theta=-\pi/2,\ \epsilon=0\) on a closed finite interval \(c_-\le c\le c_+\). Suppose that, integrating backwards, all of these frozen trajectories cross the incoming section transversely, in the same incoming branch, with bounded impact. Their corrected crossings must select a single continuous family. One sufficient way to ensure this is that at every possible crossing \(\dot{\widehat H}<0\), with \(\widehat H\) eventually above \(H\) in the past. Smooth dependence and compactness then bound the travel times for this fixed \(H\). The correction need only be defined in the large-stress region, since \(|W\cdot e|\le A\) and it can be cut off smoothly at bounded \(A\). In particular a zero of \(W\) inside the flight is allowed; integrate in \((K,V,\theta,\epsilon)\) there.

Start instead at the same seam with a small \(\epsilon_s\). Smooth dependence of the finite-time flow and transversality give the corresponding crossing and its \(\epsilon_{\rm in}\) as smooth functions of \((c,\epsilon_s)\). Since \(\dot\epsilon=O(\epsilon^2)\), one has \(\epsilon_{\rm in}(c,0)=0\) and \(\partial_{\epsilon_s}\epsilon_{\rm in}(c,0)=1\). This remains true when differentiating the crossing time because \(\dot\epsilon=0\) on the frozen trajectory. Uniformly on the compact interval, the implicit function theorem now prescribes \(\epsilon_s\) by \(c,\epsilon_{\rm in}\) for all \(0\le\epsilon_{\rm in}\le\epsilon_0\). Positive \(\epsilon_{\rm in}\) gives positive \(\epsilon_s\). Thus, at *the same incoming radius parameter as any physical shot*, the data that reach the seam form a continuous curve
\[
   c\longmapsto(\phi_\Gamma(c,\epsilon_{\rm in})\bmod P,
                 I_\Gamma(c,\epsilon_{\rm in}),\epsilon_{\rm in}).
\]
The phase has a bounded continuous real lift \(\Phi_\Gamma\) on the compact rectangle \([c_-,c_+]\times[0,\epsilon_0]\).

For a frozen seam with horizontal tangent, \(K\) is even in frozen arclength, \(V\) is odd, and the angle from that initial tangent is odd. Hence the vertical stress component is odd and the horizontal one even. Opposite signs of \((W\wedge e)/\sqrt{|W|}\) at two outgoing tails give opposite signs at their two incoming tails.

## A rectangle crossing, without phase monotonicity in the marker

Assume the physical shot from the centre hits this section continuously for all \(b\ge b_0(H)\), with phase lift \(\Phi(b)\) unbounded above on every tail, impact \(I(b)\) and \(\epsilon(b)\to0\). Suppose for the chosen \(H\) the frozen endpoint impacts straddle a closed interval strictly containing every sufficiently late \(I(b)\). By continuity this remains true at \(\epsilon(b)\), after increasing \(b_0\). Interchanging the two seam endpoints if necessary, take the negative impact at the left endpoint.

Given any \(B\ge b_0\), choose an integer \(n\) so large that \(\Phi(B)-nP<\min\Phi_\Gamma\), and \(B'>B\) with \(\Phi(B')-nP>\max\Phi_\Gamma\). On \([B,B']\times[c_-,c_+]\), put
\[
  G_1(b,c)=\Phi(b)-\Phi_\Gamma(c,\epsilon(b))-nP,\qquad
  G_2(b,c)=I_\Gamma(c,\epsilon(b))-I(b).
\]
Both functions are continuous. The first has opposite strict signs at the \(b\)-faces; the second has opposite strict signs at the \(c\)-faces. They have a common zero by the planar Poincaré–Miranda theorem. Equivalently apply Brouwer's theorem to the coordinatewise projection of \((b,c)-G(b,c)\) onto the rectangle. A fixed coordinate on either face is impossible by its strict sign, and in the interior each component must vanish.

A zero gives equality of the complete incoming states in the radial frame at the same positive \(\epsilon\). Uniqueness of the regular initial-value system therefore carries the true shot to \(V=\cos\theta=0\) later. Its positive flight from the section persists from the strictly positive frozen flights. In physical supports the reversors are \((k,v,p,q)\mapsto(-k,v,-p,-q)\) at the initial data and \((k,v,p,q)\mapsto(k,-v,p,-q)\) at the seam. If \(s_*\) is the seam arclength, their composition changes the sign of curvature after \(2s_*\); after \(4s_*\) the supports recur with total curvature zero. The reconstructed curve is closed and has turning number zero.

Since \(B\) was arbitrary, successful markers are unbounded. These solutions cannot all be covers of finitely many geometric profiles: at fixed dilation each compact profile has bounded \(|k_s|\) on every traversal, whereas the initial derivative equals \(b\). Thus the strict impact signs and the incoming estimates, once established, imply infinitely many geometrically distinct closed zero-turn homothetic expanders.
