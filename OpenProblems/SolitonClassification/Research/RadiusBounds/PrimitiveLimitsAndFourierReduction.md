# Pure expanders with bounded full geometric period

Fix the dilation coefficient at one and place its centre at the origin. A closed oriented unit-speed immersion \(X\) then obeys
\[
 T=X_s,\quad N=JT,\quad T_s=kN,\quad k_s=v,\quad v_s=-k^3/2-X\cdot N .
\]
A **full period** returns the plane position and unit tangent as well as the curvature data. The primitive full period is the smallest positive period of that immersion. A period of the curvature or support data can be shorter.

## Compactness and limits of primitive curves

Assume the full period \(L\le H\). The length-capped marked states, including multiple traversals, form a compact family in \(C^\infty(\mathbb R/\mathbb Z)\) in the unit variable \(u=s/L\). In fact the known closed-slice estimate and pure similarity identities give, with \(M=\max|k|\), \(E=\tfrac12\int k^2\), \(F=k''+k^3/2\),
\[
  \int F^2=E,\qquad \int k F=L,\qquad
  E\ge L/\sqrt2,\qquad M^6\le2^{24}E^2,\qquad E\le128^3 L^3 .
\]
The last inequality follows by inserting \(E\le LM^2/2\) in the pointwise estimate. Thus \(L\ge (2^{-1/2}/128^3)^{1/2}>0\). These estimates are those used in EnergyCappedPitchSpectrum, now applied with the cap \(EL\le128^3H^4\). Also \(\|v\|_\infty\le\sqrt{LE}+LM^3/2\) by integrating \(k''\) from a curvature critical point.

For a direct position bound, write \(p=X\cdot N,\ q=X\cdot T,\ R=\max|X|\). At a radius maximizer one has \(q=0,\ |p|=R\). Since \(p_s=-kq\), \(|p_s|\le MR\); on a following arc of length \(\ell=\min(L/2,1/(2M))\) one has \(|p|\ge R/2\). Hence \(R^2\le4E/\ell\) by \(\int p^2=E\). All six coordinates of \((X,T,k,v)\) admit explicit bounds depending only on \(H\). The polynomial ODE yields derivative bounds of every order after passage to \(u=s/L\). The limits solve the equation, satisfy \(|T|=1\), and return both \(X,T\). The winding \(w=(2\pi)^{-1}\int_0^1 Lk\,du\) is preserved along each convergent fixed-winding sequence.

If primitive full periods tend to \(L_*\), write \(L_*=dP\), where \(P\) is the primitive full period of the limit. The period group is discrete because the curve has nonzero velocity. Its winding \(w_0\) over \(P\) satisfies \(w=d w_0\). In particular the primitive family itself is compact at \(w=\pm1\). At winding zero the integer division condition imposes no restriction, but the lower bound for \(P\) above still bounds \(d\).

**Necessary resonance for a loss of primitivity.** If \(d>1\), the noncircular limiting orbit has a *primitive \(d\)-th root of unity* as a multiplier of the Poincaré return along its primitive full geometric period. This means a root whose order is exactly \(d\). Circle equilibria in support space admit no such limit of distinct primitive profiles because their normal support spectrum is hyperbolic.

Use support and frame variables \((k,v,p,q,\theta\bmod2\pi)\), with \(T=(\cos\theta,\sin\theta)\) and \(X=qT+pN\). The four-dimensional support vector field
\[
  (v,-k^3/2-p,-kq,1+kp)
\]
has zero divergence. On a noncircular orbit it never vanishes. Take a section transverse to this four-field, retaining the frame angle as the fourth section coordinate. Near a point on the full primitive orbit, restrict to a small frame-angle neighbourhood and take the return near time \(P\). At the base point its differential is block triangular with a three-dimensional support section block \(A\) and a frame eigenvalue \(+1\), since the support dynamics and return time are independent of initial angle. The support flow preserves volume, so the return preserves its transverse flux measure and \(\det A=1\) at the fixed point. The section can be chosen so small that there are no earlier full-state returns away from the time-zero and time-\(P\) flow boxes, by compactness and primitivity of the limiting orbit.

The nearby primitive closed curves therefore give cycles of exact period \(d\) for this local return \(R\), all their intersections converging to its fixed point. One way to justify the count is to fix a symmetric small time tolerance at each multiple of \(P\), follow the reference orbit over \(d\) traversals and use transversality for precisely one crossing in each box; the complementary compact time intervals stay outside the section. The \(d\)-th crossing is the given closing time. A repeated crossing earlier would violate primitivity.

Write \(D R=B\) at the fixed point and \(x_{j,i}\) for the \(i\)-th point in the \(j\)-th cycle, with subscripts modulo \(d\) and local Euclidean section coordinates. For any prime \(p\mid d\), put \(h=d/p\). Divide each difference \(x_{j,i+h}-x_{j,i}\) by the maximum norm of these \(d\) differences, which is nonzero by exact period. A subsequence yields vectors \(u_i\), some of norm one. The integral derivative formula for \(R\) gives \(u_{i+1}=B u_i\), and telescoping gives \(\sum_{l=0}^{p-1}u_{lh}=0\). On the complex span of the \(u_i\), \(B^d=I\), so \(B\) is diagonalizable there. At least one eigenvalue \(\lambda\) has \(\lambda^d=1\) and \(\lambda^h\ne1\); otherwise the telescoping sum would equal \(p u_0\), and \(u_0=0\) would force all \(u_i=0\). Its order captures the full power of \(p\) dividing \(d\).

Every nontrivial such eigenvalue belongs to the real \(3\times3\) matrix \(A\). If there is a nonreal unit eigenvalue, its conjugate is the other one and the remaining real eigenvalue is \(+1\), since \(\det A=1\). Thus the conjugate pair has a common order divisible by every prime power in \(d\), and that order also divides \(d\), proving it is precisely \(d\). If all relevant eigenvalues are real the only possibility is \(d=2\) with eigenvalue \(-1\). For a circle the independent support linearization has no imaginary-axis eigenvalues: at \(k=c,\ c^4=2\), its characteristic polynomial at \(i\xi\) equals \((\xi^2-5c^2/4)^2+7/8\). The return fixed-point equation in support variables consequently has a locally unique, constant solution even when \(L\) varies near a multiple of its period.

The conclusion concerns period multiplication. Distinct primitive orbits can still accumulate at the *same* primitive period through a degeneracy. To test an individual noncircular orbit, take the support section, its return \(\mathcal R\) near the known full period, and its lifted angle increment \(\mathcal H\). Nearby closed shapes of the same marking obey \(\mathcal R(z)=z,\ \mathcal H(z)=2\pi w\). Injectivity of the three-column differential of \((\mathcal R-\mathrm{id},\mathcal H)\) suffices for local isolation modulo rotations and phase by the inverse function theorem applied to a nonsingular three-row minor. The resonance proof does not assume this rank condition.

## A finite determining set of Fourier modes for the entire cap

There is an explicit finite-dimensional reduction even if some closed profiles are degenerate. Use the full seven-component state \(Z=(X_1,X_2,T_1,T_2,k,v,L)\) in fixed period-one coordinates with polynomial field
\[
 G(Z)=(L T,\;LkJT,\;Lv,\;-L(k^3/2+X\cdot JT),\;0).
\]
Choose a rectangular convex box containing the componentwise bounds above, with a positive interval for \(L\). Let \(C\) clip each coordinate to that box, and put \(G_c=G\circ C\). One may take any explicit upper bound \(K\) for \(\sup_{\rm box}\|DG\|\), obtained for example by bounding the Frobenius norm termwise. Then \(G_c\) is globally \(K\)-Lipschitz and bounded on Euclidean space; its pointwise action has the same Lipschitz constant on the real periodic \(L^2\) space. Choose \(N\) with \(\rho=K/[2\pi(N+1)]<1\), and let \(P_{\le N},P_{>N}\) be the componentwise real Fourier projections.

For any vector trigonometric polynomial \(y=P_{\le N}y\), the unseen modes \(h=P_{>N}h\) of a periodic solution are uniquely determined by
\[
                  h=D^{-1}P_{>N}G_c(y+h).
\]
Here \(D=d/du\), and its inverse on high modes has operator norm at most \(1/[2\pi(N+1)]\) on \(L^2\). The right side is a contraction with ratio \(\rho\); from \(h_0=0\) its iterates have error at most \(\rho^j\|h_1\|_2/(1-\rho)\) after \(j\) steps. The fixed point is \(H^1\) since the inverse gains a derivative. It varies Lipschitz-continuously with \(y\), with Lipschitz constant at most \(\rho/(1-\rho)\). In particular two marked solutions with identical low Fourier coefficients are equal, with a quantitative inverse-continuity bound.

The remaining equation is the finite collection
\[
                 D y=P_{\le N}G_c(y+h(y)),
\]
including the constant mode. Retain roots for which the reconstructed state lies in the box, \(0<L\le H\), \(|T(0)|=1\) and the required winding integral holds. Then \(D Z=G(Z)\) initially in the weak sense, hence classically and smoothly by the ODE, and \(T\cdot JT=0\) keeps \(|T|=1\). The periodic state already includes both position and frame closure. Every true profile in the cap supplies such a root; conversely each retained root reconstructs an actual closed pure expander. Primitive traversals are selected by testing the full-state period. The iteration also yields uniform enclosures of the low-mode residual on bounded low-mode boxes, with integration error included in numerical use. It can certify exclusion where that residual stays away from zero. A finite system or compact family need not have finitely many zero orbits. Near singular zeros, existence requires its own argument.

A bound on the primitive **support** period alone has a different outcome. The turning-one Andrews–Wheeler jellyfish built from seam angle \(\pi/m\) have \(2m\) arcs in the full period, and after dilation-normalizing to coefficient one each arc has length of order \(m^{-1/2}\). A pair of arcs is a support period yet the true geometric period grows on the order of \(\sqrt m\). The winding one precludes a repeated geometric traversal. The initial curvature one at the chosen seam becomes of order \(\sqrt m\) in this normalization. Thus bounded support periods and even fixed winding do not give the compactness asserted above for full periods. The signs, closure construction and length-constant calculation are documented in [Andrews and Wheeler, §2](https://arxiv.org/html/2601.21227v1#S2) and in JellyfishLengthCoefficient.md.

These are analytic arguments. They give restrictions on non-isolated periodic profiles and an explicit approximation procedure. Global isolation of every primitive homothetic closed solution has not been proved.
