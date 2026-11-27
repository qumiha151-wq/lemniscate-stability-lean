# Continuous dyadic reference paths for the winding-one candidate

The files reset_tape.py and nodes.py use the five parameters and phase of the winding-one shooting centre. They describe paths for both signs of the exact rational step $h=\pm T/4000$. The integer $D=2^{240}$ is the common denominator for all state and variational coefficients. The local time variable is $0\le z\le1$.

Each of six state polynomials and 25 nonconstant entries of the fundamental matrix has degree at most 52. The missing row and column of the matrix are the constant parameter row and the angle column. The polynomial proposals use rounded Taylor coefficients. Every endpoint is obtained by summing its polynomial coefficients as integers, and is copied to the next initial value. Thus both reference paths are continuous at every reset. The two initial states are identical and lie within $1/(2D)$ of the exact shooting centre. The initial matrix is exactly the identity.

For the state $x=(k,u,p,q,b,\theta)$ put $F=(8u,-k^3/16-p/8-bq/8,-kq,1+kp,0,k)$. For a proposed path $Q,M$ form the integer coefficient polynomials
\[
   16\,\mathrm{den}(h)D^3\,(Q'-hF(Q)),\qquad
   16\,\mathrm{den}(h)D^3\,(M'-h\,dF(Q)M).
\]
The variable in the prime is $z$. Dividing the coefficient $\ell^1$ norm by this positive common denominator bounds the supremum of a residual on its entire time cell. Use the maximum coordinate for the state, and maximum over matrix row sums for the variation.

To multiply polynomials exactly, substitute $2^{1280}$ for the indeterminate using arbitrary-precision signed integers. If $J$ is the largest sum of absolute integer coefficients of any of the 31 input polynomials, then $J\ge D$. The coefficient sum of every scaled residual entry is at most
\[
   16\,\mathrm{den}(h) D^2 (52)J + 256|\mathrm{num}(h)|J^3 .
\]
This follows from the triangle inequality for convolution, from the degree bound for differentiation, and the displayed field and its derivative. The largest field coefficient after multiplication by 16 is 128. The cubic derivative row has coefficient sum at most 9 in these units. The program checks the displayed bound is less than $2^{1279}$ on each cell. The coefficients extracted as signed base-$2^{1280}$ digits are therefore the true integer residual coefficients: reduction modulo the base recovers the constant coefficient, and subtraction and division give the induction. After degree 156 the remaining integer is zero. No bound on an omitted Taylor tail is needed. Taylor arithmetic is used solely to propose the polynomials.

The independent Lean example loads the 31 actual polynomials in the positive cell from node 2000 to 2001, verifies their exact endpoint sums and bounds every packed residual coefficient sum by $10^{-64}$ times the common denominator. The generic reconstruction theorem covers signed coefficients. The faster simultaneous test sets $T=2^{748}$ and adds $T(1+B+\cdots+B^{156})$ to the packed residual, where $B=2^{1280}$. A single integer bitwise mask certifies that each biased base-$B$ digit lies in $[0,2T)$. Subtracting $T$ gives absolute value at most $T$ at every place. The proved coefficient sum bound is $157T$, whose normalized value is less than $10^{-64}$. The proof assistant verifies both the general mask-to-sum implication and its 31 numerical instances. The remaining 7999 cells currently use the independent integer replay.

For each of the 8002 signed nodes, nodes.py checks the rational state bounds, compares the matrix row norm to 15000, constructs a rational approximate inverse $W$ on a $10^{-12}$ mesh and verifies the exact integer bounds $\|I-MW\|_\infty<1$ and $\|W\|_\infty/(1-\|I-MW\|_\infty)<15000$. Neumann's inequality proves invertibility of the actual dyadic matrix. The test also bounds radii at all nodes, counts oriented crossings of the positive real ray by the polygon of support-plane coordinates, and checks all primes up to 300 at the specified positive grid indices. The two final nodes lie strictly on the same side of the ray, so a short closing segment adds no crossings.

The state and matrix defects give a continuous-path alternative to the original Taylor-node jump budgets. For example, on each cell the error of the true solution $x$ relative to $Q$ can be written $x-Q=My$. If $e=Q'-hF(Q)$ and $B=M'-h\,dF(Q)M$, the exact equation is
\[
 y'=M^{-1}\{h[F(Q+My)-F(Q)-dF(Q)My]-e-By\}.
\]
This identity exploits global linearized transport by $M$ instead of multiplying crude scalar Lipschitz factors over 8000 steps. There is no $y$ jump when adjacent reference matrices are invertible. Identification with the particular shooting root additionally uses control between nodes, shadowing for the parameter cube, and a quantitative inverse function argument. The full dyadic replay and this note are independent integer computation and written mathematics. They do not in themselves constitute a Lean proof of the shooting root.

## Bounds obtained over the full tape

There were 4000 cells in each signed direction. On the positive side the maximum node matrix and inverse norms are at most 2107 and 3144; on the negative side they are at most 2887 and 3476. On either half, the sum of the full-cell uniform state residual bounds is below $5.43\,10^{-67}$ and the corresponding matrix sum is below $2.71\,10^{-66}$. Every node has support-plane radius greater than $0.1766$ and distance to the horizontal test ray's axis greater than $0.00105$. Both half polygon crossing counts are zero. All 62 final entries over both signs (six coordinates and 25 variable matrix entries per sign) differ from the independent Arb final reports by less than $1.50\,10^{-66}$.

Here is an explicit link to exact ODE solutions. In the physical-time tube $|k|,|u|,|p|,|q|,|b|\le(9,5,9,9,0.2)$ the field's first four speeds are bounded respectively by $40,47,81,82$, its derivative has infinity norm at most 18 and its second derivative has bilinear norm at most 4. These follow row by row from the displayed field, with the angle unrestricted. Start in the verified inner node bounds $(8.4,4.35,7.25,7.25,0.15)$ and use the residual equation to the first exit. Since $|h|<0.008$, the reference path stays strictly inside the tube, with distance greater than $0.04$ from each outer coordinate face. On a cell let $U'=h\,dF(Q)U$, $U(0)=I$. The operator norms of $U,U^{-1}$ are at most $e^{0.144}<1.16$. Variation of constants gives $\|M(z)-U(z)M(0)\|\le 1.16\sup\|B\|$. At each cell start $\|M(0)\|\le 2887$ and $\|M(0)^{-1}\|\le3476$. The elementary inverse perturbation inequality now gives $\|M\|,\|M^{-1}\|\le K=5000$ throughout every cell, including its endpoints.

At the exact centre let $r=4\,10^{-63}$. Start with $M(0)=I$ and $\|y(0)\|\le1/(2D)$. On any initial time interval where $\|y\|\le r$, the preceding transformed differential equation gives
\[
 \|y\|\le 1/(2D)+5000(5.43\,10^{-67})+
       31\cdot (4/2)\cdot5000^3 r^2 +5000(2.71\,10^{-66})r <r .
\]
Here $\sum |h|=T<31$ on a half trajectory. The tube margin allows the physical second derivative bound along the segment between $Q$ and $Q+My$. Continuation to first contact gives the estimate over all 4000 cells in either direction, hence every true centre node and intervening state is within $2\,10^{-59}$ of its dyadic reference path. The angle coordinate is unrestricted in the tube and bounded on these finite reference paths, so finite-time continuation has no escape alternative. For the actual initial-data derivative $J$, differentiation gives an equation for $M^{-1}J$ with total coefficient norm bounded by $5000(2.71\,10^{-66})+31\cdot4\cdot5000^3r<6.3\,10^{-50}$. Both matrices start at the identity. Thus the true derivative differs from its reference by at most $5000(e^{6.3\,10^{-50}}-1)<3.2\,10^{-46}$ on each half orbit. These all-cell solution and variation bounds are written estimates from the integer tape.

## Independent shooting contraction on the whole parameter cube

For parameters within $10^{-30}$ of the centre in maximum norm, the phase-line initialization changes the state by at most $10^{-30}$. Use $r=1.1\,10^{-30}$ in the same first-contact argument, adding $10^{-30}$ to its initial term. The right side is still strictly less than $r$. At every fixed centre time $\|x-Q\|\le 5.5\,10^{-27}$ and the total coefficient of the $M^{-1}J$ equation is less than $1.71\,10^{-17}$. Thus the actual initial-data derivative differs from its reference by less than $9\,10^{-14}$. Varying either final time by at most $10^{-30}$ adds at most $90\,10^{-30}$ in state and $5001(e^{18\,10^{-30}}-1)$ in its initial-data derivative. The tube margins ensure that these local time estimates apply. In particular the final state and derivative differ from the dyadic endpoints by less than $6\,10^{-27}$ and $10^{-13}$, respectively, uniformly on the parameter cube.

The five shooting residuals are the differences of rows $k,8u,p,q,\theta$ of the two endpoints, with $2\pi$ added to the last. Define an exact rational matrix $A$ by replacing the exact endpoint matrices and states at the central parameters by the dyadic values in its derivative formula, using the sum of the two endpoint fields in the half-period column. The initialization map on the other four parameters has operator norm at most one. The upper bound for the derivative difference on the entire cube is
\[
  \|DG-A\|_\infty \le 8(2\,10^{-13}+2\cdot18\cdot6\,10^{-27})<2\,10^{-12}.
\]
The program root.py inverts $A$ exactly, checks $BA=I$, and obtains $\|B\|_\infty<13$. It encloses $\pi$ via Machin's formula $\pi=16\arctan(1/5)-4\arctan(1/239)$ and the alternating-series bounds (92 and 31 terms); the formula itself follows from tangent addition with both angles on the principal interval. The centre-state shadow error contributes at most $32\,10^{-59}$ per shooting coordinate. Exact rational calculations give
\[
 \|BG(c)\|_\infty<9.64\,10^{-45},\qquad
 \sup\|I-BDG\|_\infty<2.59\,10^{-11}.
\]
Consequently the contraction $z\mapsto z-BG(z)$ maps the closed parameter cube strictly inside itself. Its unique fixed point is a true shooting zero and lies within $9.64\,10^{-45}$ of the declared centre. This is a second validated proof of the same winding-one candidate's closing equations; all 8000 polynomial cells and the final contraction use rational arithmetic. Uniform estimates for the true shooting map, the fixed-point theorem and the geometric interpretation are written mathematics in this verification.

To replay, run `python reset_tape.py 1 4000` and `python reset_tape.py -1 4000`, then `python nodes.py` and `python root.py`. Only nodes.py uses python-flint to propose rational inverse witnesses, each of which is rechecked by integer matrix products. tape_hashes.json identifies the uncompressed JSON lines. The regenerated source for the sample positive cell can be obtained with `python middle.py`.
