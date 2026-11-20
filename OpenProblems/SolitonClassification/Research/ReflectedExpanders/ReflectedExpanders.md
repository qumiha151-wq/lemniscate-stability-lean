# Twelve reflected homothetic expanders of turning number zero

There exist at least twelve geometrically distinct smooth closed immersed planar curves of turning number zero which expand homothetically under the free elastic flow. Each has two perpendicular reflection axes through its expansion centre. Each is distinct, even after rescaling or taking multiple covers, from Bernoulli's lemniscate. The existence proof combines two exact symmetries of the profile ODE with twelve validated two-dimensional shooting roots. The theorem establishes a finite lower bound on the number of shapes.

## Normalisation and shooting

Choose unit speed and let \(T,N=JT\) be the oriented Frenet frame. Put \(p=X\cdot N,\ q=X\cdot T\), and \(v=k_s\). With expansion centre at zero and dilation coefficient \(a=1\), the pure homothetic equation \(k_{ss}+k^3/2=-p\) becomes the polynomial system
\[
 z'=(v,-k^3/2-p,-kq,1+kp),\qquad z=(k,v,p,q).                 \tag{1}
\]
Given a solution, integrate \(\theta'=k\) and set \(T=(\cos\theta,\sin\theta)\), \(X=qT+pN\). Equation (1) gives \(X'=T\). The curve \((1+4t)^{1/4}X\) has the normal velocity of the free elastic flow. A tangential reparametrization gives the pure normal gauge.

Start (1) at \(z_b(0)=(0,b,0,0)\). Solve for \(b>0,t>0\) in the two equations
\[
 G(b,t)=(v_b(t),q_b(t))=(0,0).                                  \tag{2}
\]
The table gives rounded locators. Only the dyadic centres, rational radii and validated inequalities in the certificate are used in the proof.

| Initial curvature derivative \(b\) | Quarter-segment length \(t\) |
|---:|---:|
|0.201415536|9.051817414|
|0.360873137|7.548941013|
|0.719266733|5.702164307|
|0.775123005|9.333032474|
|1.186064867|10.026248280|
|2.741837898|4.798366138|
|3.779002838|5.054711877|
|4.777115283|5.979863236|
|5.722978476|6.038730692|
|6.715809618|6.930724835|
|7.609790122|6.917746422|
|8.615878048|7.760496516|

## Reflection and closure

Two commuting reversors of (1) are
\[
 R(k,v,p,q)=(k,-v,p,-q),\qquad S(k,v,p,q)=(-k,v,-p,-q).
\]
The initial point is fixed by \(S\); at a root of (2) the terminal point is fixed by \(R\). Uniqueness therefore extends the segment to a smooth analytic orbit satisfying \(z(-s)=Sz(s)\) and \(z(t+s)=Rz(t-s)\). Since \(C=RS=(-k,-v,-p,q)\) commutes with the flow,
\[
 z(2t)=(0,-b,0,0),\qquad z(s+2t)=Cz(s),\qquad z(s+4t)=z(s).
\]
In particular \(k(s+2t)=-k(s)\), so the total turning over \(4t\) vanishes exactly. Both the frame and the support coordinates recur; hence the reconstructed position closes. The nonzero initial derivative excludes a circular curve.

With \(\theta(0)=0\), the symmetry at \(s=0\) gives \(X(-s)=-X(s)\). The symmetry at \(t\) gives reflection in the normal line at \(X(t)\), since \(q(t)=0\) places this normal line through the origin. Explicitly, the tangents at \(t+s\) and \(t-s\) are symmetric about the tangent at \(t\); reversing the parameter changes this tangent reflection to the normal reflection on positions. Composing the reflection with \(X\mapsto-X\) gives the perpendicular reflection as well.

## Why the roots give different images

On a nonconstant periodic orbit, the support state is an embedded circle in phase space when parametrised modulo its least positive period \(P\). Indeed, recurrence of a state implies recurrence of the entire orbit by ODE uniqueness; its period group is closed and discrete. On that phase circle \(S\) acts by \(s\mapsto -s\). Exactly two states are fixed, at \(0\) and \(P/2\). The states at \(0\) and \(2t\) are distinct and both fixed by \(S\), hence exhaust its fixed states. A centre crossing with \(k=0\) has \(k=p=q=0\) and is therefore fixed by \(S\). Thus **every centre crossing with zero curvature has \(|k_s|=b\)**, including on every multiple cover. The argument allows \(4t\) to be a nonminimal period.

Normalisation makes this marker geometric. A homothety by factor \(\lambda>0\) changes the coefficient \(a\) to \(a/\lambda^4\). If the same closed profile is written with two centres and coefficients, subtract its two normal equations. This gives \((dX+c)\cdot N=0\) for a scalar \(d\) and a constant vector \(c\). Multiplication by \(k\) and integration yield \(d=0\), because \(\int kX\cdot N=-L\) by \(q'=1+kp\) and \(\int kN=\int T'=0\). A single nonzero constant vector tangent at every point is incompatible with closed regularity; hence \(c=0\). Consequently a similarity between two profiles normalised at \(a=1\) preserves scale and takes the centre to the centre. Reflections and reversal of orientation preserve the absolute curvature derivative. Pairwise disjoint \(b\)-intervals therefore distinguish the twelve shapes.

This comparison also distinguishes their unparametrised images. A compact regular analytic curve is covered by finitely many compact embedded subarcs. If a second regular analytic curve has the same image, the preimages of those subarcs form a finite closed cover of any compact parameter interval. One has interior. After restriction away from its two endpoints, the analytic inverse on an embedded subarc gives a local reparametrization. In unit speed it is a shift or reversed shift. Analytic continuation extends this equality over the whole real line.

For the explicit Bernoulli curve in Miura and Wheeler, \(k^3=-27p\) and the dilation coefficient is \(15/2\). Dilation to coefficient one gives \(p=-5k^3/18\). From \(p'=-kq\) it follows that \(q=5kv/6\) off its curvature zeros, and everywhere by analyticity. At a centre crossing \(k=0\), differentiating gives \(1=q'=5v^2/6\). All twelve \(b\)-intervals exclude \(\sqrt{6/5}\). [Miura and Wheeler, §2.2.3](https://arxiv.org/html/2404.12619v3#S2.SS2.SSS3)

The jellyfish constructed in Andrews and Wheeler's Theorem 1.1 use a fundamental arc with tangent angle \(\pi/m\), doubled and repeated \(m\) times. Their total turning is \(2\pi\), up to orientation. The zero-turn shapes here lie outside that constructed family. The present count does not exhaust the zero-turn pure expanders, including those possessing a reflection. [Andrews and Wheeler, §2.6](https://arxiv.org/html/2601.21227v1#S2.SS6)

## Validated shooting calculation

The verification uses Python 3.12.14, python-flint 0.9.0 and FLINT 3.6.0 real ball arithmetic. The [certificate](certificates.json) stores radii \(10^{-18}\) or \(10^{-22}\) and exact dyadic centres for all twelve boxes. The [integrator](certify.py) and [replay driver](replay.py) independently re-evaluate every box from its recorded centre. With python-flint installed, run `python replay.py` or `python replay.py --jobs 3` in this directory. The search seeds and floating-point ODE computations do not enter the certificate. This is a validated arithmetic proof, with its numerical trust boundary at the stated software.

For verification introduce \(w=(A,B,C,D)=\partial_b z_b(s)\), initially \((0,1,0,0)\). Differentiation of (1) gives
\[
 w'=(B,-3k^2 A/2-C,-qA-kD,pA+kC).
\]
At fixed \(s=t\) the endpoint Jacobian, with columns in order \(b,t\), is
\[
 DG(b,t)=\begin{pmatrix}B&-k^3/2-p\\D&1+kp\end{pmatrix}.
\]
Here smooth dependence follows from the polynomial vector field on each bounded tube.

Each integration divides \([0,t]\) into \(n\) equal steps of length \(h=t/n\). On the full two-parameter box the step length itself is an interval. The eight coordinates at the left endpoint have a current interval enclosure \(Z\). For a candidate coordinatewise radius \(w_i>0\), the program verifies
\[
 |h|\,\sup_{Y\in Z+[-w,w]} |f_i(Y)|<w_i\quad\text{for every }i.
\]
First exit and local continuation prove existence throughout the step inside this enclosure. Define \(\Phi_j(Y)\) as the \(j\)-th Taylor coefficient of the autonomous solution starting at \(Y\). They are computed by polynomial substitution in the differential equation and division of the coefficient of order \(j\) by \(j+1\). Taylor's theorem applied to each real component therefore yields the endpoint enclosure
\[
 \sum_{j=0}^{N-1}h^j\Phi_j(Z)
  + h^N\Phi_N\bigl(Z+[-w,w]\bigr).
\]
The entire resulting ball is propagated to the next step. The degree-\(N\) term uses a tube enclosing the exact real solution, including its variational coordinates. This argument does not use complex time analyticity or discard interval radii.

For a box of centre \(x_0=(b_0,t_0)\), radius \(r\) in the maximum norm and exact dyadic preconditioner \(H\), the program evaluates \(G(x_0)\) and encloses \(DG\) throughout the box. In each row it verifies
\[
 \lambda_i=\sum_j\sup |(I-HDG)_{ij}|<1,\qquad
 |(HG(x_0))_i|+r\lambda_i<r .
\]
The largest row bound among the twelve boxes is less than \(2.30\cdot10^{-11}\). Each \(H\) is verified invertible. The map \(x\mapsto x-HG(x)\) takes the closed box into its interior and is a strict contraction. Banach's theorem now gives a unique true shooting zero in each box. Exact rational comparisons verify all twelve marker intervals are disjoint and exclude the Bernoulli value. This supplies the existence input to the reflection and distinction arguments.
