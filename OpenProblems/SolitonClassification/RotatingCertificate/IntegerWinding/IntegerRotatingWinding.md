# A genuinely rotating closed elastic expander of centre winding one

There is a smooth noncircular closed expander of the planar free elastic flow with nonzero rotation, primitive curvature-support period equal to its primitive geometric period, and trivial Euclidean symmetry group of its plane image. Its signed tangent turning and winding about its similarity centre are both \(-1\) in the computed orientation and both \(+1\) in the opposite orientation. The curve stays more than \(0.152\) from that centre. This distance concerns the image. Its nonzero winding places the centre inside the convex hull.

The proof combines real ball arithmetic and analytic ODE estimates. Lean verifies the six determinant signs and the existence of three real roots for every pair of matrices in the stated rational endpoint boxes. The Arb computations and the written argument establish that the true orbit and its derivatives satisfy the bounds, and establish the winding and the geometric conclusions. A floating-point continuation identified the candidate. The existence proof uses the frozen decimal centre independently of the path of continuation. [Lean theorem](../../SolitonClassification/Rotating/IntegerWindingPencil.lean) · [Project audit](IntegerWindingVerification.json)

A subsequent Lean audit verifies the true degree-60 step on the entire candidate node box, the two first signed endpoints of the full shooting cube, and a least-period test for actual periodic supports. [Verified steps and scope](IntegerWindingStepVerification.md)

## The equation and exact shooting map

Normalize dilation to one and centre at zero. Write \(T'=kN, N=JT, p=X\cdot N, q=X\cdot T, u=k'/8\). For pitch \(b\), position is reconstructed as \(X=qT+pN\), and its derivative is \(T\). The augmented field in the order \(x=(k,u,p,q,b,\theta)\) is

\[
 f=(8u,-k^3/16-p/8-bq/8,-kq,1+kp,0,k).
\]

Fix the exact decimals \(e=-0.05995393111634394, g=-0.9982011451324311\). The unknown is \(c=(k_0,p_0,l,\alpha,b)\), the initial state is \(z=(k_0,\alpha e/8,p_0,\alpha g,b,0)\), and \(Q(k,u,p,q,b,\theta)=(k,8u,p,q,\theta)\). With \(\Phi\) the local flow, solve

\[
 G(c)=Q(\Phi(l,z)-\Phi(-l,z))+(0,0,0,0,2\pi)=0 .
\]

The centre \(c_0\) is the exact vector in [center.json](center.json). Its coordinates start \(7.7591166371, 0.1578429521, 30.2106169881, 0.1058226798, 0.1064442553\). The closed cube has infinity radius \(r=10^{-30}\). A zero has a support period \(2l\), with frame increment exactly \(-2\pi\). Thus \(X'=T\) reconstructs an actual closed unit-speed immersion, and \(k''+k^3/2=-p-bq\) is the normalized rotating-expander equation.

## Validating the two finite integrations

Use the outer tube \(|k|,|p|,|q|\le9, |u|\le5, |b|\le0.2\), with unrestricted angle. In the componentwise infinity norm the bounds for \(f,Df,D^2f\) are \(A=90, L=18, H=4\). The four varying constrained components have derivative bounds \(40,47,81,82\). Degree-by-degree majorization uses \(90(1+w/10)^3\), whose solution from zero is \(10((1-18t)^{-1/2}-1)\). Its variational fundamental majorant is \((1-18t)^{-3/2}\). These majorants give convergent solutions for \(|t|<1/18\). At a signed step \(h=\pm l_0/4000\), \(s=18|h|\), the degree-60 truncation errors for state and matrix are bounded respectively by

\[
 10s^{61}/(1-s),\qquad
 \|M_j\| s^{61}\{123/(1-s)+2s/(1-s)^2\}.
\]

The grid routine evaluates state and fundamental polynomials using Arb balls. Their exact dyadic midpoints are the next grid data. The radius of each state evaluation and the maximum row sum of the matrix radii are added to the corresponding truncation allowances before summing all jumps. The routine checks every grid state against the tighter component bounds \(8.4,4.35,7.25,7.25,0.15\), and both the full \(6\times6\) fundamental matrix and its inverse have norm below 15000 there. Since \(|h|<0.008\), the local exact trajectory cannot exit the outer tube before the next node. Every constrained moving component retains margin \(>0.05\), and pitch is constant. Along these exact local segments the fundamental and inverse norms are bounded by \(K=I=20000\) by Grönwall. The initial angle column and the invariant pitch row are restored exactly in the full matrices.

Here are the details connecting these reset grids to one true solution. Write \(S_x,S_M\) for the summed state and matrix jumps, \(d_0\) for the initial rounding, \(T_*=32, \sigma=d_0+I S_x, j=I S_M, C=IHK^2/2\). On each exact local segment from the grid data \(X,M\), put \(w=M^{-1}(x-X)\) for the single true state \(x\). Taylor's theorem gives \(|w'|\le C|w|^2\). Across a node, the affine jump has additive magnitude at most \(I\Delta_x\), and its linear part differs from the identity by at most \(I\Delta_M\). Starting with parameter displacement \(d=0\) or \(r\), the bound until first exit from \(|w|\le B\) is therefore

\[
   (d+\sigma+T_* C B^2)e^j .
\]

The checker proves this expression is strictly below \(B\) both for \(B=10^{-42},d=0\) and \(B=2r,d=r\). Consequently the true trajectory exists and stays in the tube for both signs, including the parameter cube. When a terminal time moves by at most \(r\), the additional displacement is at most \(Ar\) by continuation inside the spare margin. The angle also stays bounded over these finite intervals because \(|\theta'|\le9\). The strict inequalities give an open neighborhood of the cube on which the shooting map is smooth.

If \(P\) is the true fundamental matrix, \(M^{-1}P\) solves a linear equation with coefficient norm at most \(IHK^2 B\) on each segment. Its multiplicative jumps differ from identity in total norm at most \(j\). At the frozen centre the true endpoint-state error is at most \(E=K10^{-42}\), and the endpoint-matrix error is at most \(D=K\operatorname{expm1}(T_*IHK^2 10^{-42}+j)\). The inverse jump factors have total log-norm bounded by \(2j\) for \(j<1/4\). Uniformly on the cube these estimates with \(B=2r\), and a terminal extension by \(r\), give \(\|P\|\le4K, \|P^{-1}\|\le4I\). The checker verifies both exponential bounds.

The shooting Jacobian has initial-data part \(Q(P_+-P_-)Dz\) and length column \(Q(f_++f_-)\). The stored matrices and endpoints give centre Jacobian and residual enclosures after adding \(16D+16LE\) and \(16E\), respectively. The twice differentiated ODE, its mixed time derivative, and the ordinary time derivative of \(f\) give the uniform shooting Hessian bound

\[
 H_G=16\{T_*(4K)(4I)H(4K)^2+2L(4K)+LA\}.
\]

Take \(B_0\) to be the exact dyadic midpoint matrix of an Arb inverse of the enclosed Jacobian; the checker independently bounds \(\det B_0\) away from zero. Its certified Lipschitz factor for \(c\mapsto c-B_0 G(c)\) is \(\|1-B_0DG(c_0)\|+\|B_0\|H_G r\). This is below \(0.01\), and its product with \(r\) plus \(\|B_0G(c_0)\|\) is strictly below \(r\). The contraction theorem yields an exact zero in the cube. On this cube \(30<l<31, b>0.1, k''(0)<-200\); the curve has nonconstant curvature.

## Centre winding and least period

Write \(Z=q+ip\), so \(X=e^{i\theta}Z\). At the fractional time \(\pm jl/4000\) of the actual zero, each state coordinate is within \(K(2r)+Ar<10^{-18}\) of its stored dyadic value. Inflate both support coordinates by that amount. Their norm at every node exceeds \(0.16\). Throughout each mesh interval the radius can decrease by at most its arclength, less than \(0.008\), because the true plane curve is unit speed. Thus \(|X|>0.152\) everywhere. The angular speed of \(Z\) is bounded by \(1/|X|+|k|<16\). Each true step therefore turns through less than \(\pi/2\).

For adjacent inflated vectors \(v,w\) the dot product is certified positive. The checker sums \(\arctan(\det(v,w)/(v\cdot w))\), the signed increment of the continuous angle on that step. The positive-half sum minus the negative-half sum encloses the true total support-angle change in \((-0.001,0.001)\). Since the support closes, this change is a multiple of \(2\pi\), hence zero. The full polar winding of \(X\) is therefore \(-1\), as is its tangent turning. Orientation reversal yields \(+1\) in both formulas.

The support period is also primitive. For any nonconstant \(T\)-periodic solution of an \(L\)-Lipschitz autonomous field on a convex set, choose a phase with maximum speed \(M>0\). The average derivative is zero. Comparison with the value of the field at this phase gives \(M\le(LM/T)\int_0^T\min(t,T-t)\,dt=LMT/4\). Apply this in the five coordinates excluding the angle; their field has Lipschitz bound 18 on the tube. Thus every period is at least \(4/18\). If \(2l\) repeated a shorter support cycle, a prime divisor \(d\le2l(18)/4<300\) would make \(2l/d\) a support return. For each such prime the positive-half grid compares the initial support with the closest node to \(2l_0/d\). The componentwise derivative bounds and parameter-time displacement allow for the timing error; at least one of \(k,u,p,q\) still differs by more than \(0.001\). The individual witnesses are recorded in [plus.json](plus.json). This excludes every shorter support period.

## Symmetries of the entire image

Every Euclidean isometry preserving the plane image induces a shift or reversal of its unit-speed parametrization. Indeed the analytic immersion has finitely many preimages at each point by compactness and local injectivity. Its image locally consists of finitely many analytic arcs. The transformed analytic arc must agree with one of these on an open segment, as intersections of distinct analytic arc germs are isolated. Unit speed on that segment gives a shift or reversal, and analytic continuation extends this parametrized equality.

The geometric normal velocity is intrinsic to the curve and is unchanged under orientation reversal. An isometry \(x\mapsto A x+a\) transports the original affine field \(x+bJx\) to \(x-a+(\det A)bJ(x-a)\). Their difference must be everywhere tangent to the same curve. If \(A\) reverses orientation this difference is \(2bJ(x-z)\) for a constant \(z\), so \(\partial_s|X-z|^2=0\); the curve would be circular, contrary to the curvature check. If \(A\) preserves orientation the difference is the constant \((1+bJ)a\). A nonzero constant vector cannot be tangent everywhere to a regular closed curve, hence \(a=0\). The isometry is then a rotation about zero. The nonzero centre winding prevents it from reversing the traversal, and an oriented shift preserving the curve up to rotation returns all its supports. The primitive-period test forces the shift to be a full period. Thus the rotation fixes the curve pointwise and is the identity.

## Local classification with unrestricted closing length

There is a tube about this periodic support orbit and a pitch interval about its pitch such that the only complete support orbit at each pitch confined to the tube is the analytic continuation of this orbit. Write \(h(b)\) for its turning in revolutions during one primitive support period. It has nonzero derivative at the constructed solution, where \(h=-1\). For rational \(h=m/d\) in lowest terms the primitive closed reconstruction winds \(m\) times about the centre and has tangent turning \(m\). For irrational \(h\) the reconstruction does not close. In particular the reference shape, up to rotation, change of arclength origin and reversal of orientation, is the only closed curve of absolute centre winding one in a sufficiently small such neighborhood. This covers nearby pitches and arbitrarily many section returns of a putative confined curve.

Here are the additional checks. Let \(M_\pm\) be the \(4\times4\) support-to-support principal blocks of the true derivative at the two endpoints, at fixed time and pitch. The full fixed-time support return derivative based at the negative endpoint is \(M_+M_-^{-1}\). The file [local.py](local.py) encloses both blocks at the actual shooting root. The a posteriori root displacement is at most \(\|B_0G(c_0)\|/(1-\mathrm{Lip})\). Multiply this by \(T_*(4K)(4I)H(4K)^2+L(4K)\) and add the frozen-centre derivative error \(D\) to enclose each entry. The determinant \(\det(M_+-zM_-)\) has opposite certified signs at the endpoints of each of

\[
 (-1000,-700),\qquad(-0.001,-0.0001),\qquad(3,5).
\]

The fourth multiplier is exactly \(1\), since the nonzero support vector field at the marked point is fixed. All four roots are simple. The three multipliers of a section transverse to the support orbit therefore miss the unit circle. [Determinant enclosures](hyperbolic.json)

For completeness, take a transverse disk to the primitive orbit. Its return map and fixed point depend analytically on pitch by transversality and the implicit function theorem. Translate the fixed point to zero. In a norm adapted to its stable and unstable eigenspaces the return map is \(z\mapsto A z+g_b(z)\), with \(\|A_s\|,\|A_u^{-1}\|\le\rho<1\) for the base derivative and \(\|g_b(z)\|\le \xi\|z\|\), uniformly for nearby pitch, with \(\xi<1-\rho\). Iterating the stable equation from the infinite past and the unstable equation from the infinite future bounds the two components of any complete confined sequence by \(\xi S/(1-\rho)\), where \(S\) is its supremum norm. Thus the sequence is zero. The primitive support orbit has a smooth tubular phase with strictly positive derivative along the vector field. A smaller tube ensures that any entire orbit staying in it crosses the disk on every revolution, so the return-map result applies without a length cap.

The exact shooting derivative is invertible by the contraction bounds. Varying the final target from \(-2\pi\) to \(2\pi h\) thus gives a smooth local family \(c(h)\). Its period stays near the base primitive period and is the first section revolution by transversality. This family must be the hyperbolic continuation at pitch \(b(h)\). Therefore \(h(b(h))=h\) and both derivatives are nonzero. The support loop stays away from zero under continuation, so its integer winding remains zero. Over \(d\) blocks, \(X=e^{i\theta}Z\) now has winding \(m\); its frame returns for the first time compatible with a support return precisely at block \(d\). After shrinking to \(-3/2<h<-1/2\), the only reduced fraction in this open interval with numerator of absolute value one is \(-1\). Multiple covers also multiply the winding. These facts give the announced local uniqueness.

On each nearby rational branch the plane image has exactly the cyclic group of order \(d\) as its Euclidean symmetry group. Shrink the pitch interval so that the curvature stays nonconstant and the pitch stays positive. The earlier argument excludes all reflections and shows that every rotation fixes the centre. Since \(m\ne0\), a rotation preserves the traversal orientation, so it acts by a shift through an integer number of primitive support periods. Those shifts realize precisely the powers of rotation by \(2\pi m/d\). In particular primitive rational profiles with arbitrarily large finite cyclic symmetry occur at pitches tending to the asymmetric solution.

## Reproduction

In a clean clone, change to `OpenProblems/SolitonClassification/RotatingCertificate/IntegerWinding`. With ordinary Python 3.12, install `python -m pip install python-flint==0.9.0` into the active environment and run `python replay.py`. Use native Python assertions, with no `-O`, `-OO` or `PYTHONOPTIMIZE`. The entry point refuses optimized interpreters. It builds the two signed grids in a temporary directory, validates the root and its geometry, checks the transverse multipliers, and compares the true-matrix enclosures with all 32 rational Lean inputs. The shorter command `python replay.py --saved` performs the same downstream calculations using the archived grid reports. Add the option `--require-byte-match` to require exact agreement with the four archived reports. The default mode also accepts independently valid enclosures with different last bits when the same mathematical checks and all Lean input boxes pass. No network access is required after flint is installed. [Reproduction entry point](replay.py) · [Shared polynomial kernel](../classification_odd_branch_interval/validated_metric_shoot.py)

The complete numerical inputs for this orbit are [the frozen decimal centre](center.json), [the grid and angle calculation](trajectory.py), [the root checker](verify.py) and [the multiplier checker](local.py). [Certificate](certificate.json) · [positive half-grid report](plus.json) · [negative half-grid report](minus.json). To check the Lean theorem, run `lake build SolitonClassification.AxiomAudit` from the independent `OpenProblems/SolitonClassification` project with the toolchain pinned there. The other closed profiles outside the specified tube remain unclassified.
