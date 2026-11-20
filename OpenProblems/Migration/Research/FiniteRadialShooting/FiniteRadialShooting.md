# Finite-stress shooting from a radial section

## Certified exclusion

Normalise the dilation coefficient to one, put the actual similarity
centre at the origin, and set \(N=JT\). The profile equation is
\[
 k''+\tfrac12k^3=-X\cdot N-bX\cdot T
\]
with arbitrary constant rotation-to-dilation ratio \(b\). Parametrise
by arclength and impose the initial section
\[
 X(0)=(d,0),\quad T(0)=(0,1),\quad k(0)=k_0,\quad k'(0)=v_0 .
\]
At a positive minimum radius one can always rotate the plane and choose
the direction of traversal to obtain this form. The exclusion below only
needs such a section, whether or not the point minimises radius. It does
not impose a reflection symmetry.

**Theorem.** Every closed profile with a section in the entire parameter box
\[
  1/16\le d\le5/16,\qquad 1\le k_0\le2,\qquad
  |v_0|\le1,\qquad |b|\le2
\]
contains the closed disk of radius \(1/45056\) about its centre in its
convex hull. The same conclusion holds on all 320 closed boxes listed
in certified.json. These include 64 further boxes with \(k_0<1\) in
their interiors. Two additional boxes with strictly negative \(k_0\)
are certified separately below.

**Proof.** Use \(T=(-\sin\phi,\cos\phi)\), \(\phi(0)=0\). The actual
initial-value equation for \(z=(x,y,\phi,k,v)\) is
\[
 z'=(-\sin\phi,\cos\phi,k,v,
 x\cos\phi+y\sin\phi+b(x\sin\phi-y\cos\phi)-k^3/2).
\]
Each row of certified.json contains four endpoint pairs of integers and
two positive integers \(i,j\). Divide the endpoints by 16 to obtain the
four closed input intervals in the order \(d,k_0,v_0,b\). All other
initial coordinates are exactly zero. At the two signed arclengths the
interval computations in this folder establish
\[
 x(i/32)<-1/1024,\quad y(i/32)>1/32,\qquad
 x(-j/32)<-1/1024,\quad y(-j/32)<-1/32 .
\]
Both \(i,j\) are at most 44. Join these points \(P,Q\) to \(D=(d,0)\).
The segment \(PQ\) meets the negative horizontal axis, while \(D\) is
on the positive axis, so the origin is strictly inside the triangle.
Its distances to lines \(DP,DQ\) are at least
\(d\min(|P_y|,|Q_y|)/(44/32)\ge1/704\), by unit arclength.
The determinant \(|P_xQ_y-P_yQ_x|\) is greater than
\((|P_y|+|Q_y|)/1024>1/16384\); also \(|P-Q|\le88/32\).
The distance to the line \(PQ\) is therefore greater than \(1/45056\).
The triangle contains the claimed disk. Its three vertices lie on any
closed continuation. Hence every later similarity hull shares the
centre with the initial hull. A proof of periodicity is unnecessary for
this exclusion.

**Outward-bending boxes.** Around either of
\[
 (d,k_0,v_0,b)=(1/8,-1/2,-2,0),\qquad(1/8,-1/2,2,-2),
\]
give all four coordinates independent closed uncertainty \(1/128\).
At the first box take \(P=X(-2),Q=X(3/4)\); at the second take
\(P=X(2),Q=X(-1/2)\). The checker establishes that
\(\det(D,P),\det(P,Q),\det(Q,D)\) have common strict sign and
magnitudes above \(1/1024\). Thus these triangles also contain the
origin in their interiors, uniformly over their boxes. In these two
cases the initial signed curvature bends away from the centre.

## Verification and replay

The two programs use Python 3 and python-flint 0.9.0. All geometric
inequalities use outward-rounded Arb intervals. The executable
certificate requires only the checkers and certified.json; the
numerical search, a native compiler, NumPy, and SciPy are unnecessary
for its replay.

1. Run \(\texttt{python certify.py}\) to regenerate certified.json with
   the order-two integrator at 112 bits and step \(h=1/32\). The grid
   intervals for \(d,k_0,v_0,b\), respectively, have lower integer
   endpoints \(1,2,3,4\); \(8,12,16,20,24,28\);
   \(-16,-8,0,8\); and \(-32,-16,0,16\), and widths \(1,4,8,16\),
   all divided by 16. The resulting \(4\cdot6\cdot4\cdot4=384\)
   cells yield 320 certified triangles. Reflection across the horizontal
   axis composed with reversal of arclength sends \((v_0,b)\) to
   \((-v_0,-b)\) and \((x,y)\) to \((x,-y)\), which the first checker
   uses for the negative endpoint.
2. Run \(\texttt{python replay.py}\) to verify every listed row independently.
   This checker imports no code from the first integrator, uses 144 bits,
   and integrates forward **and backward** with signed step
   \(\pm1/64\). It uses a third-order Taylor enclosure and recomputes all
   geometric margins. Its output replay.json confirms all 320 rows,
   including all 256 product cells in the displayed full box, with no
   further subdivisions in this run. The same checker separately verifies
   the two negative-curvature boxes on their complete input intervals.

Both implementations first enclose the local trajectory by a Picard
box \(B\) satisfying \(z+[0,h]f(B)\subset B\), with the interval
reversed for negative steps. They enclose the step endpoint by Taylor's
formula with the highest derivative evaluated on that entire box.
In the second checker put \(p=X\cdot N,\ q=X\cdot T\). The required
identities are \(p'=-kq,\ q'=1+kp\). If \(A=k''\) and \(B_1=k'''\),
\[
 A=-p-bq-k^3/2,\qquad
 B_1=kq-b(1+kp)-3k^2v/2,
\]
\[
 k''''=vq+k(1+kp)-b(vp-k^2q)-3kv^2-3k^2A/2 .
\]
Polynomial arithmetic, sine and cosine, all initial intervals and all
step sizes in the two checks use Arb enclosures of rational inputs.
Inconclusive bounds are never accepted as successful inequalities.
These are validated numerical enclosures external to Lean.

## Two rotating candidate neighbourhoods

The two boxes below use the variables \(p=X\cdot N,\ q=X\cdot T,\ T=(\cos\theta,\sin\theta)\), satisfying \((k,v,p,q,\theta)'=(v,-k^3/2-p-bq,-kq,1+kp,k)\).

The exact decimal
centres of two five-dimensional boxes are in edge3_intervals.json, in
the order \(k_0,v_0,p_0,q_0,b\), with \(\theta(0)=0\).
The independent radii in the five jet coordinates are respectively
\(2^{-28}\) and \(2^{-30}\). Their rational witness arclengths, in units of \(1/128\), are
\((0,-1056,1072)\) and \((0,-1048,1096)\). For each box the checker
certifies that the three consecutive determinants of the *actual*
positions at the witness arclengths all exceed \(1/256\). In particular
every periodic continuation of any jet in either certified box has the
origin strictly inside its convex hull. The warrant attaches to these
initial-value boxes; an exact closed orbit at the numerical root
estimates has not been established. No entire one-sided curve was found.

Run \(\texttt{python edge3_transport.py}\) in this directory, using the
same python-flint installation. It reads only the two fixed interval
inputs and the polynomial field and jet recursion in edge3_hull.py.
The validated path does not use the continuation, a compiled library,
NumPy, or SciPy. The exact input radii and outward-rounded determinant
enclosures are written to edge3_certificates.json. Each determinant
endpoint is stored as integers \((m,e)\) denoting exactly \(m\,2^e\).

The transport computation adjoins \(b'=0\), divides the six coordinates
by \(8,64,8,8,1,1\), and uses a Picard enclosure for all initial points in
the current box. Along a step its interval \(A=hDf\) contains all
scaled Jacobians evaluated on that enclosure. The ordered-integral
series for the derivative of the flow map lies in
\[
 I+\sum_{m=1}^6 A^m/m!+[-\delta,\delta]^{6\times 6},\qquad
 \delta=\frac{r^7}{7!}\frac1{1-r/8},\quad r=\|\,|A|\,\|_\infty<1 .
\]
Here the products are interval matrix products. They enclose products
at independently varying times, and integration over the ordered time
simplex gives the factor \(1/m!\). This applies in both time directions
after rescaling each step to \([0,1]\). The image of the exact centre
is bounded by Taylor's formula through order eight plus the order-nine
term on the whole tube. If \(Q\) and \(Q_1\) are consecutive coordinate
bases, the new error is enclosed by the transformed centre remainder
plus \((Q_1^{-1}D\Phi_h Q)\) times the preceding interval error.
Gram–Schmidt selects dyadic basis entries; the interval inverse is
checked before use. No exact orthogonality is required. No accumulated
error is discarded in the change of basis.

This certificate verifies an exclusion on the stated parameter sets. The general existence of a closed migrating flow remains open.
