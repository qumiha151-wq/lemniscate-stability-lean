# Tree-like limits of length-normalized curves at escaping records

Let \(X(t)\) be one smooth closed free elastic flow with positive limiting bending energy \(E_\infty>0\). Let \(t_j\to\infty\) be global record times for \(U=EL\) with \(U(t_j)\to\infty\). Parametrize each slice by fractional arclength, subtract a base point and divide the position by \(L(t_j)\). Every uniform subsequential limit is a **tree-like closed path** in the sense of Hambly and Lyons. Equivalently, every nonempty word in the two coordinate differentials has zero iterated integral on the limit. Subsequence limits exist by the unit Lipschitz bound. The statement permits a nonconstant limit going out and returning on a tree.

There is a quantitative extension to escaping records even when \(E_\infty=0\). If their normalized slices converge to a path which is not tree-like, passage from a sufficiently smaller preceding record takes at least \(cU(t_j)\) terminal RMS time units and costs at least a fixed positive fraction of the bending energy. A positive limiting bending energy and such a subsequence are incompatible. [Physical swept-area and record estimates](WindingAreaRecords.md)

## Matrix transport of a closed path

For real skew-symmetric \(n\)-by-\(n\) matrices \(A,B\) and a plane loop \(x=(x_1,x_2)\), solve on its parameter interval \([0,1]\)
\[
 V'(u)=V(u)\big(Ax_1'(u)+Bx_2'(u)\big),\quad V(0)=I,\qquad M_{A,B}(x)=V(1).
\]
Orthogonality of \(V\) follows by differentiating \(VV^T\). Its endpoint changes by conjugation on moving the base point, by inversion on reversing orientation, and stays fixed after translation of the whole curve. Write \(\|\cdot\|\) for the Euclidean operator norm and define
\[
 J(x)=\sup_{\substack{n\ge1,\ A,B\in\mathfrak{so}(n)\\ [A,B]\ne0}}
             \frac{\|M_{A,B}(x)-I\|}{\|[A,B]\|}.
\]
For a dilation by \(\lambda>0\), replace \(A,B\) by \(\lambda A,\lambda B\) to obtain \(J(\lambda x)=\lambda^2 J(x)\). Under a plane orthogonal transformation the transformed pair is an orthogonal linear combination of \(A,B\); its commutator changes by at most a sign. Thus rigid motions and the choice of starting label preserve \(J\).

If \(H(v,u)\) is any smooth homotopy of closed curves from \(x\) to \(y\), then
\[
       |J(y)-J(x)|\le\int_0^1\int_0^1|\det(H_v,H_u)|\,du\,dv.                \tag{1}
\]
For a fixed matrix pair put \(P=AH_{1,u}+BH_{2,u}\), \(Q=AH_{1,v}+BH_{2,v}\) and \(V_u=VP\). As \(P_v=Q_u\), direct differentiation gives
\[
 \partial_u\big((V_v-VQ)V^{-1}\big)=V[Q,P]V^{-1},
 \qquad [Q,P]=[A,B]\det(H_v,H_u).
\]
Denote \(Q(v,0)=Q(v,1)=Q_0(v)\), let \(M=V(v,1)\), and solve \(C_v=CQ_0\), \(C(0)=I\). Integration in \(u\) bounds the operator norm of \(M_v+Q_0M-MQ_0\) by \(\|[A,B]\|\int|\det(H_v,H_u)|du\). This is also the norm of \((CMC^{-1})_v\). Integration in \(v\), the reverse triangle inequality for the distance from \(I\), and the supremum prove (1). Conjugation accounts for arbitrary material base-point motion in this argument.

The linear homotopy between two loops with synchronized parameter and pointwise separation at most \(d\) gives \(|J(x)-J(y)|\le d(L_x+L_y)/2\). These formulas extend to Lipschitz loops in the linear comparison by smooth periodic convolution. Indeed convolution preserves an upper bound for variation, gives uniform convergence, and converges in \(W^{1,1}\) for each Lipschitz loop. Integrating the transport ODE shows convergence of its endpoint under this last approximation for each fixed matrix pair. The estimate for the endpoint distance is uniform after division by the commutator norm, so it passes to the supremum.

The radial homotopy from the arclength centroid gives \(0\le J(x)\le L_x^2/(4\pi)\), by the same Wirtinger estimate as for winding area. For the material spacetime homotopy the right side of (1) is precisely the swept area \(\int_s^t\int |F|ds\,dv\). Thus every energy-loss, crossing-time and conditional growth estimate in [WindingAreaRecords.md](WindingAreaRecords.md) remains valid with \(J\) in place of the winding area, including the exponent \(1/(3+4\pi a)\). At escaping records and \(E_\infty>0\), \(J(X(t_j))/L(t_j)^2\to0\). By homogeneity and the linear-homotopy bound, every normalized limit \(x\) has \(J(x)=0\).

## Detection of every iterated integral

For a bounded-variation loop \(x\), define its coefficient \(I_{i_1\cdots i_k}\) by integration of \(dx_{i_1}(u_1)\cdots dx_{i_k}(u_k)\) on \(0<u_1<\cdots<u_k<1\). The transport for \(\lambda A,\lambda B\) has the absolutely convergent power series
\[
 I+\sum_{k\ge1}\lambda^k\sum_{i_1,\ldots,i_k\in\{1,2\}}
       I_{i_1\cdots i_k}(x)\,A_{i_1}\cdots A_{i_k},
 \qquad A_1=A,\quad A_2=B.
\]
Iterating the integral equation proves this expansion. The \(k\)-fold integrated operator norm is bounded by \((C L_x)^k/k!\) for each fixed pair. Vanishing of all nonempty coefficients gives \(J(x)=0\).

Conversely assume \(J(x)=0\). All noncommuting matrix pairs have identity transport. Commuting pairs have identity transport on every closed path, as their transport is the ordinary exponential of the net displacement multiplied by the pair. For a chosen word \(w=i_1\cdots i_k\), number the standard basis \(0,\ldots,k\). Set **the superdiagonal entry** \((r-1,r)\) of \(A_{i_r}\) to one, its transpose entry to minus one, and every other entry of both matrices to zero, apart from these instructions for all \(r=1,\dots,k\). In a product of \(k\) factors only the steps \(0,1,\dots,k\) contribute to its \((0,k)\) entry; each step has coefficient one exactly when its letter is the corresponding letter of \(w\). The coefficient of \(\lambda^k\) in that matrix entry is therefore \(I_w(x)\). Identity transport for all \(\lambda\) forces it to vanish. Hambly and Lyons' uniqueness theorem for bounded-variation paths identifies trivial signature with a tree-like path. [Hambly and Lyons, *Annals of Mathematics* 171 (2010), 109–167](https://annals.math.princeton.edu/2010/171-1/p02)

For a non-tree-like limit \(x\), \(J(x)>0\) and the normalized slices along the convergent subsequence have \(J(X(t_j))/L(t_j)^2\ge J(x)/2\) eventually. Choosing \(q>1\) with \(d=J(x)/2-1/(4\pi q^2)>0\) supplies the quantitative cost and time bounds from the first paragraph. There is also a uniform statement over all shapes. Let \(\mathcal K\) be the compact space of based closed one-Lipschitz plane paths on \([0,1]\), and let \(\mathcal T=\{x\in\mathcal K:J(x)=0\}\). For each \(\varepsilon>0\) for which \(\{x\in\mathcal K:\operatorname{dist}_\infty(x,\mathcal T)\ge\varepsilon\}\) is nonempty, \(J\) has a positive minimum \(a(\varepsilon)\) on that set. Consequently the same energy and time costs hold uniformly for records whose normalized paths stay \(\varepsilon\) from every tree-like loop, with no need to prescribe a limiting shape. With positive limiting energy, this distance tends to zero along all escaping records.

One consequence uses ordinary chord lengths. Inner distance on the label circle is denoted \(d_{\mathbb T}\). If on an escaping sequence of product records the normalized curves satisfy \(|x_j(u)-x_j(v)|\ge c\,d_{\mathbb T}(u,v)\) for all \(d_{\mathbb T}(u,v)\le h\), with constants \(c,h>0\) common to the sequence, then \(E_\infty=0\). A uniform limit retains that local lower bound. A tree-like circle map factors continuously through a real tree, and therefore cannot be locally injective everywhere. Indeed local injectivity would make its factor into the tree locally injective too. At a point maximizing distance to any fixed tree point, a small embedded interval in the tree containing that point in its interior is a geodesic arc. Distance to the fixed point strictly increases on at least one side of any interior point of a nontrivial geodesic arc, contradicting maximality. Thus a positive limiting energy forces loss of uniform local chord control along escaping records. The argument requires no derivative convergence.

## Frequency of records away from tree-like paths

There is a further conclusion when the limiting bending energy is zero. Let \(R(t)=\max_{0\le v\le t}U(v)\), \(H(t)=R(t)/E(t)\), and let \(j(t)=J(X(t))/L(t)^2\). The functions \(R,H\) are positive, nondecreasing and locally absolutely continuous. Also \(L\le H\) and \(L=H\) on the support of \(d\log R\). The sweep bound \(|J'|\le S\) and \(2\pi S/L^2\le-(\log E)'\) give
\[
 4\pi\int_0^t j(v)\,d\log R(v)\le \log\!\frac{E(0)}{E(t)}+\tfrac12.        \tag{2}
\]
Indeed integrate \(2\pi J'/H^2\), integrate by parts, and use \(d\log H=d\log R-d\log E\ge d\log R\). The lower boundary term is at least \(-1/2\) since \(J(0)/H(0)^2\le1/(4\pi)\). For records whose normalized paths are at least \(\varepsilon\) from the tree-like set, \(j\ge a(\varepsilon)\). Equation (2) therefore bounds the total logarithmic measure of the corresponding record levels. In particular, if \(R(t)\to\infty\) and \(\log(E(0)/E(t))=o(\log(R(t)/R(0)))\), their logarithmic fraction tends to zero for every fixed \(\varepsilon>0\). This rate condition allows \(E(t)\to0\).

## A loop with identically zero winding function and \(J>0\)

Starting at the origin, let \(a\) be the square with displacements \(+e_1,+e_2,-e_1,-e_2\). Let \(b\) be the square with displacements \(-e_1,-e_2,+e_1,+e_2\). Concatenate \(aba^{-1}b^{-1}\). Its winding number is zero at every point off the trace because each square is traversed in both orientations. Nonetheless, its iterated integral for the word \(xxyxy\) is exactly \(1\).

This coefficient is computed by carrying the five nonempty prefix integrals \((I_x,I_{xx},I_{xxy},I_{xxyx},I_{xxyxy})\) across the sixteen segments, starting with zeros. For a segment with displacement \((p,q)\) use \(d I_{wi}=I_w\,dx_i\) and \(I_{\varnothing}=1\), integrating the polynomials on the segment. The final vector is \((0,0,0,0,1)\). This establishes \(J>0\) on this specific zero-winding path. The example concerns a possible Lipschitz limiting shape; the cornered polygon is not proposed as smooth initial data.

The matrix homotopy estimate and the application of the bounded-variation signature theorem are written proofs. The physical swept-area inequalities and the finite rational coefficient of the example have separate Lean checks. These restrictions on a hypothetical escaping orbit allow tree-like limits, including a single point, and permit energy decay to zero.
