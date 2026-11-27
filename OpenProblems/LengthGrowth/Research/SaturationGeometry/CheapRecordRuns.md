# Long runs of strict product records with arbitrarily small energy expenditure

Write $U=EL$ for a smooth closed planar free elastic flow. For every integer $M>0$, every $\eta>0$ and every $T_0>0$, there is a smooth primitive closed curve of turning number one and initial energy one with the following property. From its initial time until the end of a finite interval contained in $[T_0,\infty)$ its product is strictly increasing. On that late interval $\sqrt U$ crosses at least $M$ consecutive integer levels and the total energy loss from the initial time is smaller than $\eta$. The initial products in this family grow. The construction gives a genuine finite stretch of a single flow for each choice of data. It does not put all the stretches on one trajectory.

There is also a sharp scale for an individual step. There exist constants $c,C>0$ and arbitrary large $N$ for which $\sqrt{U(0)}\asymp N$ and the late interval has $c\le\sqrt{U(t_2)}-\sqrt{U(t_1)}\le C$, with relative energy loss between $c/N^2$ and $C/N^2$. The same construction with a fixed sufficiently large multiple of $1/N$ as perturbation ensures at least one complete integer level crossing. Thus attempts to exclude unbounded product by a universally nonsummable energy price for each unit step of $\sqrt U$ meet a physical finite-interval obstruction. A single orbit may have additional constraints on concatenating steps.

## One cell in a fixed coordinate

Use an arclength coordinate $\xi\in[0,2\pi]$ on one rotating cell with $ds=l(t)d\xi$, and write $p=lk$, $Q=p_{\xi\xi}+p^3/2$, $C=\langle pQ\rangle$, $e=\langle p^2\rangle/2$. Angle brackets mean the average over $[0,2\pi]$. Let $d\tau=l^{-4}dt$ and choose the tangential speed $l^{-3}H$ with $H_\xi=C-pQ$, $\langle H\rangle=0$. The arclength and signed-curvature equations give exactly
\[
 p_\tau=-Q_{\xi\xi}+(Hp)_\xi,\quad (\log l)_\tau=C,\quad
  (\log E)_\tau=-\langle Q^2\rangle/e,\quad
  (\log U)_\tau=C-\langle Q^2\rangle/e .                            \tag{1}
\]
Indeed $F=l^{-3}Q$, $k_t=-F_{ss}-k^2 F+l^{-3}H k_s$, and $(\log l)_t=kF+(l^{-3}H)_s$. For $N$ cells the whole length and energy are $L=2\pi Nl$ and $E=2\pi Ne/l$; consequently $U=(2\pi N)^2e$. In particular the equation governing $p$ on a cell has no coefficient depending on $N$. Its mean $\langle p\rangle$ is conserved.

Fix the periodic unit-amplitude-scale oscillator by writing $a(m)=2K(m)/\pi$, where $K(m)$ is the complete elliptic integral in the parameter convention. Set
\[
  \delta=(2m-1)a(m)^2,\qquad w_\delta(\xi)=2a(m)\sqrt m\,\mathrm{cn}(a(m)\xi\mid m).
\]
At $m=1/2$ the derivative $d\delta/dm=2a(1/2)^2$ is positive; the smooth local inverse defines $w_\delta$ for small $|\delta|$. It has period $2\pi$, $w_\delta(\xi+\pi)=-w_\delta(\xi)$, and $w_\delta''+w_\delta^3/2=\delta w_\delta$. These follow from the Jacobi elliptic cosine equation. [NIST DLMF, differential equations](https://dlmf.nist.gov/22.13) · [NIST DLMF, periods](https://dlmf.nist.gov/22.4)

Take $p(0,\xi)=w_\delta(\xi)+h$ and $l(0)=1$. For $h=1/N$, $N\ge2$, these are genuine smooth closed unit-speed initial data. Integrate the curvature to a tangent angle, then integrate the unit tangent. Each cell's tangent is the preceding tangent rotated by $2\pi/N$, so the $N$ cell displacements sum to zero. The turning number is one and excludes any multiple covering. Rotation about the centre of this cell isometry preserves the geometric flow, by uniqueness; its scalar cell equation is (1). Equivalently the periodic solution of (1) reconstructs the rotating cell directly: choose the angular base constant so $\theta_\tau=-Q_\xi+Hp$, set $X_\xi=l(\cos\theta,\sin\theta)$ and choose the time-dependent integration constant to realize $X_\tau=l(-QN+HT)$. The two prescriptions for $X_{\xi\tau}$ agree by (1). Thus undoing the tangential coordinate change yields the physical normal flow.

## Uniform positive time at small forcing

When $(\delta,h)=(0,0)$, $p=w_0$ is stationary in (1), with $Q=C=0$. This unclosed translation-periodic base is used to control the scalar equation on a fixed compact circle; every example claimed in the theorem has $h=1/N$ and closes exactly. Local smooth parameter dependence holds on one common interval $[0,T]$. For clarity,
\[
 H=-pp_\xi+\partial_\xi^{-1}\big(C+p_\xi^2-p^4/2\big),
\]
where the primitive of the zero-mean expression has mean zero. The nonlinear part after $-p_{\xi\xi\xi\xi}$ is a smooth map $H^4\to H^2$ on the circle, as follows by differentiating the polynomials and bounded periodic antiderivative. The periodic biharmonic semigroup gains two derivatives with bound $C(1+t^{-1/2})$. The Duhamel contraction on $C([0,T];H^4)$ is uniform on a ball around $w_0$ and depends smoothly on both input parameters by its linearized contraction. Higher regularity is obtained the same way for smooth data. In particular $Q$ in $C([0,T];H^2)$, $e$ and $C$ are continuously differentiable in $(\delta,h)$ with continuous parameter derivatives in time.

At the initial cell
\[
 Q=\delta w_\delta+\tfrac32h w_\delta^2+\tfrac32h^2 w_\delta+\tfrac12 h^3,
 \qquad
 C=(\delta+3h^2)\langle w_\delta^2\rangle+h^4/2.
\]
Odd powers have zero average. Put $A=\langle w_0^2\rangle>0$. At $(0,0,0)$, $\partial_\delta C=A$ and $\partial_h C=0$. On a smaller common time interval and parameter neighborhood $\partial_\delta C>A/2$, $|\partial_h C|<A/8$. Since $C(0,0,\tau)=0$ identically, whenever $0<h\le\delta$ are sufficiently small one gets $c\delta\le C\le C_1\delta$ throughout this interval. Parameter dependence also gives $\|Q\|_2\le C_2\delta$ and upper and positive lower bounds on $e$ independent of these parameters. Cauchy–Schwarz applied to $\langle pQ\rangle$ gives the matching bound $\langle Q^2\rangle\ge c_2\delta^2$. After decreasing the parameter range, (1) therefore proves throughout $0\le\tau\le T$ that
\[
 c_3\delta\le(\log U)_\tau\le C_3\delta,\qquad
 c_4\delta^2\le-(\log E)_\tau\le C_4\delta^2 .                     \tag{2}
\]
All four constants and $T$ work simultaneously for the whole family. The small perturbations also have exactly two simple curvature zeros per cell on this time interval by $C^1$ closeness to $w_0$.

It follows that on $T/2\le\tau\le T$ the gain of $\sqrt U$ is bounded above and below by fixed positive multiples of $N\delta$, and the relative energy loss from the start is comparable to $\delta^2$. Take $\delta=N^{-1/2}$ to produce a run across arbitrarily many integer record levels at arbitrarily small relative energy expense. Take $\delta=K/N$ for a fixed $K\ge1$ to obtain the individual-step scale, choosing $K$ large enough to cross any chosen fixed number of levels. The physical time before any rescaling is comparable to $\tau$ because $(\log l)_\tau=O(\delta)$ and $l(0)=1$. Dilation by the initial energy $2\pi Ne(0)\asymp N$ fixes initial energy one and multiplies time by a quantity comparable to $N^4$. Thus the indicated interval is arbitrarily late even measured in units of the fixed initial energy. Its strict increase makes every slice there a new record relative to the entire flow since time zero. No long-time conclusion for any one of these examples follows by increasing $N$.
