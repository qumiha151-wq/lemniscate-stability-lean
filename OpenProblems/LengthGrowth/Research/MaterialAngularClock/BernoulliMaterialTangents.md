# Tangent motion in the relative energy clock of a genuine free elastic flow

## The Bernoulli expander

Let \(E=\frac12\int k^2ds\), \(D=\int F^2ds=-E'\), and take pure-normal material labels. Write \(\theta\) for a local lift of the directed tangent angle. On the evolving Bernoulli lemniscate one has the exact identity
\[
  \inf_{c\in\mathbb R}\sup_j
  \left|\frac{E(t)}{D(t)}\,\partial_t\theta(t,j)-c\right|=\frac32
  \qquad(t\ge0).
\]
Thus even at arbitrarily late selected times a common rotation cannot make the material angular velocity small relative to the fractional rate of energy loss. On this same flow \(EL\) is constant. The identity concerns the material tangent. The geometric image is a dilation at every time.

For completeness, put
\[
 \beta(u)=\frac{\cos u}{1+\sin^2u}(1,\sin u),\quad
 h(t)=(1+30t)^{1/4},\quad \xi=\log h(t)=\log\frac{E(0)}{E(t)} .
\]
Here \(h\beta\) satisfies the free elastic flow in normal velocity, and its length and energy are \(hL(0)\) and \(E(0)/h\). The normal gauge is \(X(t,j)=h(t)\beta(u(\xi,j))\), where eliminating tangential velocity gives
\[
 u_\xi=-\frac{\beta\cdot\beta'}{|\beta'|^2}
       =\frac{2\sin u\cos u}{1+\sin^2u}.
\]
The smooth periodic right-hand side generates a global family of diffeomorphisms of the parameter circle, starting at the identity. This gives actual pure-normal material trajectories. The expanding solution and its coefficient appear in [Miura and Wheeler, §2.2.3](https://arxiv.org/html/2404.12619v3#S2.SS2.SSS3).

The directed tangent angle is \(\Theta(u)=\pi/2+3\arctan(\sin u)\). Consequently \(\Theta_\xi=6s(1-s^2)/(1+s^2)^2\) with \(s=\sin u\). For \(w=|s|\le1\) the difference \((1+w^2)^2-4w(1-w^2)=(w^2+2w-1)^2\) proves the bound \(3/2\). Both endpoints are attained at \(s=\pm(\sqrt2-1)\). Surjectivity of the label map on each time slice proves the stated minimax value. In physical time this also gives \(\int_0^T\sup_j|\theta_t|dt=\tfrac38\log(1+30T)\), even though the known \(L_t^{4/3}\) norm is finite.

For any single label the total angular motion over the entire future is at most \(3\pi/4\). Indeed the drift is monotone within each open quarter, between a zero of \(\sin u\) and a zero of \(\cos u\), and the change of \(\Theta\) on each such interval is \(3\pi/4\). Nevertheless there is no sequence of diverging times on which the material tangents converge uniformly, even after arbitrary common rotations. On \(0<u<\pi/2\) the increasing function \(H(u)=\sin u/\cos^2u\) satisfies \(H(u(\xi,j))=e^{2\xi}H(j)\). For any fixed \(0<u_*<\pi/2\), choose \(j_\xi=H^{-1}(e^{-2\xi}H(u_*))\). Then \(j_\xi\to0\), the label zero stays fixed, and their tangent-angle difference stays equal to \(3\arctan(\sin u_*)>0\). Postcomposition by a rotation preserves this chord distance. Uniform convergence on the compact circle would imply equicontinuity for the chosen sequence. Time-dependent changes of the material parameter do remove this effect.

The independent Lean module checks the explicit Cartesian derivatives, identification of the actual tangent angle, the pure-normal material angle derivative, both sharp extrema, and minimax compensation in the relative energy clock of the dilated profile. The scalar ODE produces the global label parametrization; the argument about equicontinuity is given above. [Lean source](../../LengthGrowth/ActualFlow/LemniscateAngularClock.lean) · [Project verification](AngularClockVerification.json)
