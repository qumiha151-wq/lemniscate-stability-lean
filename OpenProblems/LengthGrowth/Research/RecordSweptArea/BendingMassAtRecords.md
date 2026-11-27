# Concentration of bending energy and rates of approach to a positive plateau

Consider one smooth closed planar free elastic flow. Let \(E=\int k^2\,ds/2\), \(L=\int ds\), \(F=k_{ss}+k^3/2\) and \(D=\int F^2\,ds=-E'\), with normal velocity \(-FN\). Fix a spatial origin \(O\). If \(e_*=\lim_{t\to\infty}E(t)>0\) and \(g(t)=E(t)-e_*\), then
\[
  \lim_{t\to\infty}t^{1/15}g(t)=+\infty,\qquad
  \limsup_{t\to\infty}t^{1/17}g(t)=+\infty.                       \tag{1}
\]
At any escaping sequence of global \(EL\)-record times \(t_j\), the bending probability measures \(k^2\,ds/(2E)\) pushed forward by \(X\mapsto(X-O)/L(t_j)\) converge weakly to the point mass at zero. Moreover \(D(t_j)L(t_j)^3/E(t_j)^2\to\infty\). The [tree-like record theorem](../RecordSweptArea/TreeLikeRecordLimits.md) separately concerns the normalized positions along the curve. Every positive plateau also forces
\[
 \int_T^\infty K(t)D(t)\,dt=\infty\quad(T>0),\qquad
 K(t)=\frac{\sqrt{L(t)\int k^4\,ds}}{\int k^2\,ds}.                 \tag{2a}
\]
Thus a bounded relative fourth curvature moment on a time tail, or its square root \(K\) merely integrable against the finite energy-loss measure, suffices for \(E_\infty=0\). The arguments below permit arbitrary turning number.

## Energy outside a ball

Write \(e=k^2/2,\ p=k_s\), and set
\[
 A(t)=\int_0^t(D^{2/3}+D^{3/4})\,dv,\qquad B(t)=\int_0^t D^{1/2}\,dv,
 \qquad H(t)=1+A(t)+\sqrt{B(t)} .
\]
For each \(\varepsilon>0\) there is \(K_\varepsilon<\infty\) such that at all times
\[
  \int_{\{|X-O|\ge K_\varepsilon H(t)\}}e\,ds\le\varepsilon .      \tag{2}
\]
This estimate holds for any limiting energy. Fix \(r\) greater than twice the initial radius. Choose a smooth radial \(\chi(X)\) centered at \(O\), zero on the ball of radius \(r/2\), one outside radius \(r\), valued in \([0,1]\), with derivatives through order two bounded by \(C_j/r^j\) for \(j=1,2\). From the [material local energy identity](../SpatialLocalization/ExponentialLocalization.md),
\[
 \frac d{dt}\int\chi e\,ds=-\int\chi F^2\,ds
 -\int F[2p\nabla\chi\cdot T+3e\nabla\chi\cdot N+
                           k\,\nabla^2\chi(T,T)]\,ds .               \tag{3}
\]
Indeed \((e\,ds)_t=[-F^2+(pF-kF_s)_s]ds\); differentiating \(\chi(X)\) and integrating the flux twice gives (3). The [stress estimate](../../LengthGrowth/ActualFlow/ArclengthCoercivity.lean) gives \(\|k\|_\infty^6\le 2^{24}ED\), hence \(\int k^4\le C D^{1/3}\). Periodic integration gives \(\int p^2=\tfrac12\int k^4-\int kF\le C(D^{1/3}+D^{1/2})\). Spatial Cauchy–Schwarz in (3) and time integration bound the exterior energy by \(C[A(t)/r+B(t)/r^2]\). Choose \(r=K_\varepsilon H(t)\) separately for each terminal time, holding it fixed in the integration. This proves (2). For \(0<p<1\), \(\int_0^t D^p=o(t^{1-p})\) by splitting at a fixed late time, using Hölder and \(\int_0^\infty D<\infty\). Thus \(H(t)=o(t^{1/3})\).

## Localized dilation and concentration at records

There is \(c>0\), allowed to depend on the flow and on \(e_*>0\), such that
\[
                        D(t)\ge \frac{c}{L(t)H(t)^2}.                \tag{4}
\]
The length variation gives \(L(t)\le L(0)+\sqrt{2E(0)}B(t)\), hence \(\sqrt L\le C H\). Multiply the ambient field \(X-O\) by a smooth radial cutoff equal to one through radius \(r\), zero beyond \(2r\). The resulting vector field \(V\) obeys \(|V|\le2r,\ |\nabla V|\le C,\ |\nabla^2 V|\le C/r\). Its first variation is
\[
 \int FN\cdot V\,ds=\int [kN\cdot\nabla^2 V(T,T)
       +k^2N\cdot\nabla V N-\tfrac32k^2T\cdot\nabla V T]\,ds .
\]
Indeed the fractional speed variation is \(T\cdot\nabla V T\) and the tangent angle variation is \(N\cdot\nabla V T\). Differentiate \(\int k^2ds/2\) using both expressions. Inside the ball the integrand is \(-e\). Its full integral differs from \(-E\) by at most \(C E_{\rm ext}+(C/r)\sqrt{L E_{\rm ext}}\), where \(E_{\rm ext}=\int_{\{|X-O|\ge r\}}e\,ds\). Choose \(\varepsilon\) small enough relative to \(e_*\), and take \(r=K_\varepsilon H(t)\), with \(K_\varepsilon\) increased so \(r\ge\sqrt L\). By (2) the error is at most \(e_*/2\). Cauchy–Schwarz gives \(e_*/2\le2r\sqrt{LD}\), proving (4).

Write \(L_j=L(t_j)\). Earlier lengths are at most \(L_j\) at a global product record, since energy decreases. Ordinary dilation about a point on the curve gives \(E^2\le DL^3\) at each earlier time. Integrate over \([t_j/2,t_j]\) to obtain \(t_j/L_j^3\le 2g(t_j/2)/e_*^2\to0\). Hence \(H(t_j)/L_j\to0\). Apply (2) for every \(\varepsilon>0\) and use \(E(t_j)\ge e_*\) to obtain the stated weak limit. Equation (4) gives the diverging scaled dissipation.

## Energy escapes every disk of fixed physical radius

In the original plane all the bending energy leaves every disk of fixed radius, uniformly in centers that may move with time. More precisely, on any smooth regular closed curve, with \(M=\|k\|_\infty,\ J=\int k_s^2\,ds\), one has
\[
 \sup_z \frac{1}{E}\int_{\{|X-z|\le r\}}e\,ds
 \le C r(M+\sqrt{J/E})
 \le C' r\big[(E D)^{1/6}+(D/E)^{1/4}\big] .                       \tag{6}
\]
To see the first inequality, put \(d=(M+\sqrt{J/E})^{-1}>0\). On each arclength segment of length \(d\) the tangent angle stays within one radian of its angle at the right endpoint, since \(Md\le1\). Projection onto that endpoint tangent has derivative at least \(\cos 1>1/2\). The set of labels in this segment that map into any radius-\(r\) disk thus has length at most \(4r\). For every \(s\), integration of \(k_s\) followed by Cauchy–Schwarz gives
\[
 k(s)^2\le \frac{2}{d}\int_s^{s+d}k(v)^2\,dv+2d\int_s^{s+d}k_s(v)^2\,dv.
\]
Integrate over the preimage of the disk in a full period and interchange integrals using periodic extension. Each \(v\) sees only the admissible starts in its preceding segment of length \(d\), of measure at most \(4r\). The result is at most \(C r(E/d+dJ)\), proving (6). The second estimate uses the stress inequality and \(J\le E M^2+\sqrt{2 E D}\). Multiplying (6) by \(E\) bounds the absolute local energy by \(C r(E^{7/6}D^{1/6}+E^{3/4}D^{1/4})\). Every actual global flow has \(E(t)\le E(0)\), and [physical force persistence](../ForcePersistence/ForceDissipationPersistence.md) proves \(D(t)\to0\); the finiteness of \(\int D\) alone would not prove this pointwise limit. Hence the absolute local energy tends uniformly to zero for each fixed \(r\), including on a positive energy plateau. When \(E_\infty=0\) it also follows immediately from the bound by \(E(t)\). When \(E_\infty>0\) the conclusion holds for the normalized probability as well, while at global product records the scale \(L_j\) captures that probability arbitrarily close to the normalized origin.

## A fourth-moment criterion for energy decay

First we prove the concentration criterion (2a). Return to (3) without bounding the \(L^2\) norms by powers of \(D\), and put
\[
 P(t)=\|k^2\|_2+\|k_s\|_2,\qquad
 H_*(t)=1+\sqrt{1+B(t)}+\int_0^t P(v)\sqrt{D(v)}\,dv .
\]
The same argument gives (2) with \(H_*\) in place of \(H\). In particular \(\sqrt L\le C\sqrt{1+B}\le C H_*\), and the localized dilation proof gives \(D^{-1/2}\le C\sqrt L H_*\). Therefore \(D^{-1/4}\le C H_*\). Since \(\int k_s^2=\tfrac12\int k^4-\int kF\), we have \(P\le C[(\int k^4)^{1/2}+D^{1/4}]\). Each term of \(H_*'\) is now controlled as follows:
\[
 \frac{\sqrt D}{\sqrt{1+B}}\le C D H_*,\qquad
 (\textstyle\int k^4)^{1/2}\sqrt D\le C K D H_*,\qquad
 D^{3/4}\le C D H_* .
\]
For the middle estimate insert \(D^{-1/2}\le C\sqrt L H_*\) and \(2E\le2E(0)\). Consequently \((\log H_*)'\le C(1+K)D\). Integration yields
\[
 \int_T^t K D\,dv\ \ge\ c\log L(t)-C_T.                             \tag{5}
\]
On a positive plateau \(L(t)\to\infty\): \(2e_*\le L(t)\|k(t)\|_\infty^2\) and [uniform straightening](../PhysicalWidth/WidthAndGrowth.md) gives \(\|k(t)\|_\infty\to0\). This proves (2a). The argument also bounds the middle term above by \(C(\int k^4)^{1/2}D^{3/4}H_*\), using \(D^{-1/4}\le C H_*\). Thus even the integral of the pointwise minimum of \(K D\) and \((\int k^4)^{1/2}D^{3/4}\) diverges on every tail under the same hypothesis.

## The bound at all late times

First \(g(t)\ge c t^{-1/6}\) for large \(t\) by integrating (4) on \([t,2t]\) with \(H(v)\le C v^{1/3}, L(v)\le C\sqrt v\). Fix \(0<b\le1\) and write \(S=bt/g(t)^2\), so \(S>2t\) eventually. For \(t\le v\le 2S\), Hölder gives
\[
 L(v)\le L(t)+C S^{1/2}g(t)^{1/2},\qquad
 H(v)\le H(t)+C[S^{1/3}g(t)^{2/3}
                 +S^{1/4}g(t)^{3/4}+S^{1/4}g(t)^{1/4}].
\]
For the last term use \(\sqrt{B(t)+h}\le\sqrt{B(t)}+\sqrt h\). Since \(L(t)=o(\sqrt t)\), \(H(t)=o(t^{1/3})\), and \(g(t)\ge c t^{-1/6}\), for each fixed \(b\) and all sufficiently large \(t\),
\[
  \sup_{[S,2S]}L\le C b^{1/2} t^{1/2}g(t)^{-1/2},\qquad
  \sup_{[S,2S]}H\le C b^{1/3}t^{1/3}.
\]
Here \(C\) can be chosen independently of \(b\). In particular the two fourth-root terms are \(O_b(t^{1/4}g^{1/4}+t^{1/4}g^{-1/4})=o_b(t^{1/3})\). Integrating (4) over this window gives \(g(t)\ge c b^{-1/6}t^{-1/6}g(t)^{-3/2}\). Therefore \(\liminf t^{1/15}g(t)\ge c' b^{-1/15}\). Let \(b\downarrow0\).

## The upper-envelope rate

Suppose \(g(t)=O(t^{-1/17})\). On \([v,2v]\), the increase of \(A\) is at most \(C(v^{5/17}+v^{7/34})\), since \(1/3-(2/3)/17=5/17\) and \(1/4-(3/4)/17=7/34\). The increase of \(B\) is \(O(v^{8/17})\). Dyadic summation gives \(H(t)=O(t^{5/17})\), \(L(t)=O(t^{8/17})\).

In fact \(L(t)=o(t^{8/17})\) by the [slow-window doubling obstruction](../SaturationGeometry/SlowWindowLengthRigidity.md). Otherwise choose \(t_j\to\infty\) with \(L(t_j)\ge d t_j^{8/17}\), \(d>0\). Choose a fixed small \(\theta>0\) such that \(L(\theta t_j)<L(t_j)/2\). Take the last half-length time \(s_j\) thereafter before \(t_j\) and the first full-length hit \(u_j\) after it. Put \(m_j^2=2E(s_j)/L(s_j)\), \(\delta_j=1-E(u_j)/E(s_j)\). Then \(\delta_j\to0\), and \((L(u)-L(s))^2\le(u-s)(E(s)^2-E(u)^2)\) implies \(m_j^4(u_j-s_j)\to\infty\). Yet \(m_j^4(u_j-s_j)\delta_j\le C t_j g(\theta t_j)/L(t_j)^2=O(1)\), contradicting slow-window length rigidity. This proves the little-oh bound. Integrating (4) on \([t,2t]\) now gives \(t^{1/17}g(t)\to\infty\), contrary to the hypothesized upper bound. This proves (1).

## Verification scope

Lean checks the complete [weighted bending flux](../../LengthGrowth/ActualFlow/BendingCutoffFlux.lean) for an arbitrary smooth weight of one Cartesian coordinate, on a genuine smooth material solution of normal free elastic flow. It checks the [projected dilation identity](../../LengthGrowth/ActualFlow/ProjectedDilation.lean) on each closed arclength slice, with an arbitrary smooth scalar profile. Adding the two coordinate cutoff energies detects the exterior of a square. Adding the two test field components \(v_r(x_i)e_i\), with \(v_r(x)=x\) through \(|x|=r\), supported in \(|x|\le2r\), gives the localized dilation on that square with the same error bounds. Both modules passed the kernel with only propositional extensionality, classical choice and quotient soundness. The integrated cutoff estimates, fourth-moment criterion, disk escape and infinite-time conclusions above have written proofs. Slower convergence to a positive limit and the unrestricted fourth-root length problem remain open.
