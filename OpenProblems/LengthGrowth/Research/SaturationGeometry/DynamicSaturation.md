# Saturated length growth persists on every fixed fast time interval

Use \(E=\frac12\int k^2\,ds,\ D=\int F^2\,ds,\ F=k_{ss}+k^3/2,\ U=EL\), and set \(\eta=LU'/E^3\). Consider a sequence of smooth closed planar free elastic flows at chosen starting slices with \(U_j\to\infty,\ U_j'\ge0\). Write \(E_0=E(0)\), \(\epsilon=U(0)^{-1/3}\), and measure subsequent time by \(\tau=(\epsilon E_0)^4t\).

**Theorem.** If \(\eta_j(0)\to1/2\), then on the actual forward flow, for every finite \(R>0\),
\[
 \sup_{0\le\tau\le R}|\eta_j(\tau)-1/2|\longrightarrow0.               \tag{1}
\]
Smooth closed turning-one examples attain these hypotheses. In particular actual increasing product records can persist arbitrarily close to the maximal rate throughout arbitrarily many fast time units across a sequence of flows. At every single time of every flow \(\eta\le1/2\), by completing a square in \(F\). The assertion concerns a sequence of initial data.

There is a persistence conclusion without saturation as well. Each increasing initial record gives locally uniform slow stress profiles as in [the spatial profile theorem](RecordStressProfiles.md). For every fixed \(R\) these profiles are stationary throughout \(0\le\tau\le R\) when their origins follow the corresponding material labels. This uses force evolution across a true time interval.

## Forward estimates in fast coordinates

Apply the single constant spatial dilation \(\epsilon E_0\); keep a pure normal material parametrization with initial arclength labels. Denote the resulting curvature, arclength derivative, force, force mass, energy and length by \(K,\partial_x,q,d,e,\ell\), respectively. The arclength \(dx\) at later \(\tau\) evolves. Initially
\[
 \ell=\epsilon^{-2},\qquad e=\epsilon^{-1},\qquad d\le2\epsilon .
\]
The normalized true curvature and its arclength derivative \(P=K_x\) are uniformly bounded at the initial times by the stress and local derivative bounds in the spatial theorem. The exact evolution identities give
\[
 e'=-d,\quad \ell'=\int Kq\,dx,\quad K_\tau=-q_{xx}-K^2q,\qquad
 d'+\int q_{xx}^2\,dx\le (36\|K\|_\infty^4+8\|P\|_\infty^2)d.        \tag{2}
\]
The last inequality follows from differentiating the force and periodic integration by parts. All time derivatives of fields in (2) are material derivatives.

Fix \(R\). There are constants depending on \(R\) and the initial uniform jet bounds such that throughout \(0\le\tau\le R\) for all sufficiently large indices,
\[
 d\le C_R\epsilon,\qquad \int_0^R\!\!\int q_{xx}^2\,dx\,d\tau\le C_R\epsilon,\qquad
 \|K\|_\infty+\|P\|_\infty\le C_R,\qquad
 \|K(\tau)-K(0)\|_{L^2(dx_0)}\le C_R\sqrt\epsilon .                 \tag{3}
\]
Here \(dx_0\) is the initial arclength on the fixed material labels. We detail the continuation to arbitrary fixed \(R\). Take \(B_0\) to bound all initial curvature maxima, set \(B=B_0+1\), and take \(H\) strictly greater than both the initial slope bounds and \(2B+B^3+2\). Up to the first time that either \(\|K\|_\infty=B\) or \(\|P\|_\infty=H\), (2) and Grönwall imply the two bounds for \(d,\int q_{xx}^2\). Since \(|\ell'|\le\sqrt{2ed}\le C_R\), one has \(\ell=\epsilon^{-2}+O_R(1)\). Periodic integration by parts bounds \(\|q_x\|_2^2\le\|q\|_2\|q_{xx}\|_2\). Consequently the time integrals of \(\|q\|_2,\|q_x\|_2,\|q_{xx}\|_2\) are all \(O_R(\sqrt\epsilon)\). The elementary one-dimensional bounds
\[
 \|q\|_\infty^2\le d/\ell+2\|q\|_2\|q_x\|_2,\qquad
 \|q_x\|_\infty^2\le2\|q_x\|_2\|q_{xx}\|_2
\]
give \(\int_0^R(\|q\|_\infty+\|q_x\|_\infty)\,d\tau=O_R(\sqrt\epsilon)\) on the same stopped interval. The second bound uses a zero of the periodic derivative. The material density satisfies \(\partial_\tau\log(dx/dx_0)=Kq\), and the material tangent satisfies \(T_\tau=-q_xN\). The density ratio and the tangent therefore differ from their initial values by \(O_R(\sqrt\epsilon)\) uniformly. The equation for \(K_\tau\) now gives the \(L^2(dx_0)\) estimate in (3).

Both the initial and current curvatures are uniformly Lipschitz in the initial label because of the slope bound and density comparison. An \(L^2(dx_0)\) difference tending to zero between two such functions on these long circles tends uniformly to zero: a fixed-height deviation would persist on an interval of fixed positive length. Thus \(\|K\|_\infty\le B_0+o(1)\) before the stop, uniformly in time. For the slope, apply the fundamental theorem of calculus to \(K\) on a current arclength interval of length one and use \(P_x=-K^3/2+q\). This gives
\[
 \|P\|_\infty\le2\|K\|_\infty+\tfrac12\|K\|_\infty^3+\|q\|_2.
\]
Both stopping thresholds are avoided for all sufficiently large indices, proving (3). The constants may depend on \(R\).

## The limiting stress during this window

Write \(y=\epsilon x\) for slow arclength at each current time and use the same material label as spatial origin at every time. Let \(y_0\) be its initial counterpart. The map between these coordinates and its derivative tend to the identity on each compact interval, uniformly in \(\tau\). On the full material circle the \(L^2(dy_0)\) difference of \(K\) between times \(0,\tau\) is \(O_R(\epsilon)\), by (3). Its \(L^2(dy_0)\) norm stays bounded. The slow stress \(V=(K^2/2)T+PN\) obeys the exact identity
\[
 V=\tfrac32 K^2 T+\epsilon\,\partial_y(KN).
\]
When integrated against a compactly supported smooth test function, the derivative term is \(O_R(\epsilon)\). The remaining term has the same limit at arbitrary moving times \(0\le\tau_j\le R\) as at zero, by the density, coordinate, curvature and tangent comparisons just proved. Also \(\int |\partial_y V|^2\,dy=d/\epsilon=O_R(1)\), since \(\partial_x V=qN\). The pointwise bounds in (3) give uniform local compactness for \(V\). Hence in every frame whose initial stresses converge locally uniformly, the stresses converge to the same profile locally uniformly, uniformly over the entire time interval. This includes each separated frame from the spatial theorem. The conclusion describes the macroscopic stress; the next-order scalar force can still evolve.

## Persistence of the maximal growth rate

In these fast initial units the completion in the spatial theorem gives \(\int (q-\epsilon K/2)^2dx=o(\epsilon)\) when \(\eta(0)\to1/2\). In slow measure \(dy=\epsilon dx\), \(W=V-\epsilon T/2\) therefore satisfies \(\|W_y\|_2=o(1)\) and \(\|W\|_2=O(1)\). The latter follows from the initial global stress bound in the spatial proof and \(\|\epsilon T\|_2=\sqrt\epsilon\). The mean point and the fundamental theorem of calculus give \(\|W\|_\infty^2\le\epsilon\|W\|_2^2+2\|W\|_2\|W_y\|_2=o(1)\). Thus initially \(\|K\|_\infty+\|P\|_\infty=o(1)\). The uniform curvature comparison in (3) and its slope estimate show that the same holds throughout \(0\le\tau\le R\). The initial square completion and \(\int K^2 dx=2/\epsilon\) also give
\[
 C(0):=\int Kq\,dx=1+o(1),\qquad d(0)/\epsilon=1/2+o(1).
\]
Now (2) implies \(d(\tau)\le(1+o(1))d(0)\) uniformly. To control \(C=\int Kq\,dx\), use the material force equation
\[
 q_\tau=-q_{xxxx}-\tfrac52 K^2q_{xx}-5KP q_x
 -(3P^2+4K K_{xx}+\tfrac32K^4)q .
\]
The two \(K^2q^2\) terms from \(\partial_\tau K\) and \(\partial_\tau dx\) cancel when differentiating \(C\). Periodicity and \(K_{xx}=q-K^3/2\) give
\[
 C'=-2\int(q+K^3)q_{xx}-5\int K^2Pq_x
   -3\int KP^2q-4\int K^2q^2+\tfrac12\int K^5q .
\]
Here and in this display all spatial integrals use current arclength. Each integral on the right has time integral \(o(1)\) in absolute value. Indeed \(\|K\|_2=O(\epsilon^{-1/2})\), \(\|K\|_\infty+\|P\|_\infty=o(1)\) and the three force norms in (3) have time integrals \(O_R(\sqrt\epsilon)\). Hence \(C=1+o(1)\) throughout the window. Since \(\ell=\epsilon^{-2}+O_R(1)\) and \(e=\epsilon^{-1}+O_R(\epsilon)\),
\[
 \eta=\frac{\ell}{e^2}C-\frac{\ell^2}{e^3}d\ge\frac12-o(1).
\]
The exact square-completion upper bound gives (1).

## Actual closed curves attaining saturation

Fix a large-amplitude odd periodic solution \(b\) of \(b''+b^3/2=b/4\) with \(\langle b^2\rangle>1\). Such solutions exist by setting \(b(s)=a w(as),\ w(0)=0,\ w'(0)=1\): \(w''+w^3/2=w/(4a^2)\), and its period and mean square tend to those of the nonzero quartic oscillator as \(a\to\infty\). For instance its first integral is \(w'^2=1-w^4/4+w^2/(4a^2)\). If \(B>0\) is the turning amplitude, substituting \(w=B\sin\theta\) gives the quarter-period weight \(2(B^2+B^2\sin^2\theta-a^{-2})^{-1/2}d\theta\), which tends uniformly to the positive limiting weight. The same quadrature with an additional \(w^2\) handles the mean square.

Write \(p\) for the period of \(b\). On \([-mp-1,mp+1]\) take \(k_m=\chi_m b\), where \(\chi_m\) is smooth and even, equals one on \([-mp,mp]\), and vanishes to infinite order at the endpoints, with uniformly bounded first two derivatives. The signed turn of this packet is zero. Its bending mass minus its length tends to infinity, since \(\int(k_m^2-1)=2mp(\langle b^2\rangle-1)+O(1)\). Attach a fixed smooth flat-ended curvature bump with integral \(\pi\), then add one flat straight segment of the nonnegative length that makes the half-block length equal to its integrated \(k^2\). Concatenate two identical half-blocks. Their tangent fields cancel after the \(\pi\) turn across a half-period, so integration yields an exactly closed smooth unit-speed immersion of turning number one. Its length \(\ell_m\) tends to infinity and \(\int k_m^2=\ell_m\).

On the exact periodic core \(F=k_m/4\); the two cutoff regions and fixed turning bump have bounded residual and bounded length, and the straight segment contributes zero. Accounting for both blocks, \(\int(F-k_m/4)^2=O(1)\). Thus \(U=\ell_m^2/2\to\infty\) and
\[
 \eta(0)=\frac12-\frac{8}{\ell_m}\int(F-k_m/4)^2\longrightarrow\frac12 .
\]
Starting the genuine smooth free elastic flow from each immersion gives (1) by the preceding proof. If desired one may choose a diagonal subsequence and a window \(R_j\to\infty\) on which the same uniform convergence holds. Each of these flows is increasing throughout its indicated window. Control from one window to later record heights on one fixed trajectory remains outstanding.

These are written analytic proofs. Formula (1), the time-uniform stress limit, and the saturating initial construction have not been verified in Lean.

The physical force-dissipation variation and its closed-curve spatial estimates are checked separately. The compactness, continuation on the fast time scale and closing construction above are written arguments. [Actual force dissipation](../../LengthGrowth/ActualFlow/ActualForceDissipation.lean) · [Spatial force estimate](../../LengthGrowth/ActualFlow/ForceRateSpatial.lean) · [Curvature slope estimate](../../LengthGrowth/ActualFlow/ForceRateSlope.lean)
