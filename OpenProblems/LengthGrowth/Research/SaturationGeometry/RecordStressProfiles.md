# Stress profiles on increasing energy–length records

Let \(k\) be the signed curvature of a smooth closed planar free elastic flow. Write \(F=k_{ss}+k^3/2,\ D=\int F^2ds,\ E=\frac12\int k^2ds,\ L=\int ds,\ U=EL\), with normal speed \(-F\). Consider any sequence of slices with \(U_j\to\infty\) and \(U'_j\ge0\). These conditions hold at first hits of arbitrarily high levels whenever \(U\) is unbounded. Put \(\eta_j=L_j U'_j/E_j^3\). The results below hold for arbitrary such slices and require no time convergence.

Let \(u\) denote the solution of \(u''+u^3/2=0,\ u(0)=0,\ u'(0)=1\). It is periodic. Write \(\gamma\) for the period mean of \(u^2/2\). Then \(1/3\le\gamma\le1/\sqrt3\). One consequence of the stress profile estimate is
\[
 \limsup_{j\to\infty}
 \left[
 U_j^2 \left(\frac{\max |k_j|}{E_j}\right)^6+
 \frac{3}{\gamma}\eta_j
 \right]\ \le\ \frac{3}{2\gamma}\ \le\ \frac92 .
 \tag{1}
\]
The static pointwise stress estimate alone gives \(U_j^2(\max|k_j|/E_j)^6\le 2^{25}\). Formula (1) also controls the simultaneous cost of record growth and curvature peaks. The estimate below for separated profiles detects the cost of changing their stress directions.

## Two spatial scales and an exact budget

First dilate each slice by its current \(E_j\). Until the final return to physical units we use \(s,k,F,D\) for the dilated quantities. Thus \(E=1,\ L=U,\ D=D_{\rm physical}/E_{\rm physical}^5\). Set \(\epsilon=U^{-1/3}\) and take
\[
 y=\epsilon^2s,\quad K=k/\epsilon,\quad P=k_s/\epsilon^2,\quad
 f=F/\epsilon^4,\quad V=(K^2/2)T+PN .
\]
All slow variables are periodic on a circle of length \(\epsilon^{-1}\). In this section a prime denotes differentiation in \(y\). Let \(J\) denote counterclockwise rotation by \(\pi/2\), so \(N=JT\). Direct substitution in the Frenet and stress equations yields
\[
 \epsilon K'=P,\quad \epsilon P'=-K^3/2+\epsilon f,\quad
 \epsilon T'=KN,\quad V'=fN,\quad |V|^2=P^2+K^4/4.
\]
The length and energy variations give an exact square completion on each full circle,
\[
 \int K^2\,dy=2,\qquad
 \int (f-K/2)^2\,dy=\frac12-\eta,\qquad
 (V-\epsilon T/2)'=(f-K/2)N .                                    \tag{2}
\]
Indeed \(U'_{{\rm dilated}}=U'_{{\rm physical}}/E_{{\rm physical}}^4
=\epsilon^3\int(K f-f^2)\,dy\). In particular \(0\le\eta\le1/2\) and \(\int f^2\le2\).

The existing stress estimate \(\max|k|^6\le2^{24}D\) now bounds \(\|K\|_\infty\) uniformly. Integrating \(\epsilon(KP)'=P^2-K^4/2+\epsilon K f\) gives \(\int P^2\le\frac12\int K^4+2\epsilon\), hence uniform global \(L^2\) bounds for \(V\) and \(V'\). Averaging on intervals of length one and applying Cauchy–Schwarz bounds \(\|V\|_\infty\) uniformly. For any chosen slow origins one may extract a locally uniform and weakly \(H^1_{\rm loc}\) stress limit \(V_*\) on \(\mathbb R\). Each such limit belongs to \(H^1(\mathbb R)\). The same extraction works for countably many origins by a diagonal argument.

At the smaller scale \(x=\epsilon s\), translated profiles of \(K\) have uniformly bounded curvature and first \(x\)-derivative \(P\). The squared \(L^2(dx)\) norm of the rescaled forcing \(F/\epsilon^3\) on the full circle is \(D/\epsilon^5\le2\epsilon\). Thus every sequence of origins has a \(C^1_{\rm loc}\) converging subsequence in \(x\) and its limit solves \(K_{xx}=-K^3/2\). To see the derivative convergence directly, integrate \(P_x=-K^3/2+F/\epsilon^3\) on compact \(x\)-intervals. Its nonzero solutions are all phase translates of \(\sqrt a\,u(\sqrt a\,x)\), with \(a=(K_x^2+K^4/4)^{1/2}>0\); the first integral and separation of variables give finite traversal time of a quarter period. They have infinite bending energy on the line, whereas the identically zero solution has zero energy. These are precisely the straight and rectangular elastica spatial limits after fixing the initial tangent and origin. In the fixed energy units \(s\), all curvature maxima tend to zero by the earlier static estimate. The nonzero smaller-scale limits can occur because their rescaled total curvature-squared integral is \(2/\epsilon\).

## Curvature mass and the direction of the force

Pass to a subsequence with \(\eta_j\to\eta_*\). In any slow frame write \(A=|V_*|\) and \(e=V_*/A\) on \(A>0\). The limiting measures there obey
\[
 K_j^2/2 \ \rightharpoonup\ \gamma A,\qquad
 N_j\otimes N_j \ \rightharpoonup\
 C_e=\tfrac23 e\otimes e+\tfrac13(Je)\otimes(Je).                 \tag{3}
\]
The first convergence holds on all compact intervals, including \(A=0\).

Here are details of the averaging. On any compact interval the pair \((K_j,P_j)\) is uniformly bounded. After extraction its bounded continuous functions have weak-star limits given by measurable probability distributions \(\nu_y\). One can obtain these distributions by diagonal weak-star compactness for polynomials with rational coefficients on a fixed compact rectangle, then uniform polynomial approximation, positivity and the Riesz representation theorem. Since \(|V_j|^2=P_j^2+K_j^4/4\) converges uniformly, \(\nu_y\) is supported on \(p^2+z^4/4=A(y)^2\) for almost every \(y\).

For any smooth test \(g(z,p)\) on a neighborhood of that rectangle,
\[
 \epsilon \partial_y g(K,P)=P g_z(K,P)-K^3 g_p(K,P)/2+\epsilon f g_p(K,P).
\]
Pairing with a compactly supported smooth function of \(y\) gives \(\int (p g_z-z^3 g_p/2)\,d\nu_y=0\) almost everywhere. One full-measure set works for all such tests by separability in \(C^1\). On a nonzero level the oscillator vector field never vanishes and traverses a single smooth periodic orbit. In its time coordinate the identity says that the measure annihilates all periodic derivatives. Every smooth test on the orbit extends smoothly to a neighborhood, so the only probability satisfying this condition is uniform time measure. At \(A=0\) the law is concentrated at the origin. Orbit scaling now gives \(\int z^2/2\,d\nu_y=\gamma A(y)\).

On \(A>0\) put \(u_0=K^2/(2|V|),\ w_0=P/|V|\) for each approximant with nonzero stress. In the approximating frame \(e_j=V_j/|V_j|\) one has \(N_j=w_0e_j+u_0Je_j\). On the oscillator, the mean of \(w_0 u_0\) vanishes by integrating the derivative of \(K^3\). Integration of the derivative of \(KP\) gives \(\langle w_0^2\rangle=2\langle u_0^2\rangle\), and their squares sum to one. Thus their respective means of squares are \(2/3,1/3\), proving the second formula on compact subsets of \(A>0\). Finally \(0\le u_0\le1\) gives \(1/3\le\langle u_0\rangle=\gamma\le1/\sqrt3\).

## Separated profiles share the same budget

Consider any finite or countable family of slow origins whose mutual distances on the approximating circles tend to infinity. Write \(V_i,A_i,e_i\) for simultaneous subsequential limits in those frames and put \(Z_i=\{A_i>0\}\). Then
\[
 \gamma\sum_i\int_{\mathbb R} A_i\,dy\le1,\qquad
 \sum_i\int_{Z_i}\left\{\tfrac32 |A_i'|^2+
       3 |V_i'-(e_i\cdot V_i')e_i|^2\right\}dy
 \le\frac12-\eta_* .                                                \tag{4}
\]
The mass inequality follows from (3) on finite collections of disjoint compact windows and total mass \(\int K_j^2/2=1\). For the second inequality choose compactly supported smooth vector tests \(\psi_i\) in \(Z_i\), first for a finite family. On their disjoint windows use
\[
 (f-K/2)^2\ge2(f-K/2)(N\cdot\psi_i)-(N\cdot\psi_i)^2.
\]
The linear term converges after integration by (2) and integration by parts. The quadratic term converges by (3). Optimizing \(2V_i'\cdot\psi_i-\psi_i\cdot C_{e_i}\psi_i\) in \(L^2\) yields \(V_i'\cdot C_{e_i}^{-1}V_i'\). Smooth compactly supported tests are dense in \(L^2(Z_i)\) and the eigenvalues of \(C_{e_i}\) lie between \(1/3\) and \(2/3\). Exhaustion and monotone convergence prove (4). The radial derivative of an absolutely continuous vector norm is \(A_i'=e_i\cdot V_i'\) almost everywhere in \(Z_i\), and is zero almost everywhere on its complement.

Every \(A_i\) is nonnegative in \(H^1(\mathbb R)\cap L^1(\mathbb R)\) and tends to zero at both ends by uniform continuity and integrability. At a peak of height \(H_i=\|A_i\|_\infty\), integrate \((A_i^{3/2})'\) to each end. Cauchy–Schwarz gives
\[
 \frac43 H_i^{3/2}\le
 \left(\int A_i\right)^{1/2}\left(\int |A_i'|^2\right)^{1/2},
 \quad
 \sum_i H_i^{3/2}\le \frac34\sqrt{\frac{2}{3\gamma}(1/2-\eta_*)}.       \tag{5}
\]
Center one slow frame at a point of maximum \(|K_j|\). Since \(K_j^2/2\le |V_j|\), its limiting peak is at least \(\limsup \|K_j\|_\infty^2/2\) upon taking a subsequence attaining the limsup. Applying (5) proves (1), including the simultaneous \(\eta_j\) term by subsequence selection.

The alternative is quantitative. Along any sequence of increasing records, the following three limits are equivalent:

1. \(U^{1/3}\max |k_{\rm physical}|/E_{\rm physical}\to0\).
2. The supremum over all slow translates of the curvature-squared mass on a unit slow interval tends to zero.
3. Every subsequential locally uniform limit of the translated slow stress is identically zero.

The first implies the second by the length of that interval. Failure of the third violates the second by (3) on an interval where \(A>0\). Failure of the first gives a translated nonzero limit by centering at a curvature maximum. If these conditions fail, each family of increasingly separated nonzero peaks must satisfy (5), which bounds the number of peaks above any fixed threshold. The estimates allow both complete spreading on the slow scale and localized oscillator packets with a finite envelope cost. Their creation, persistence and interaction between successive records are outside these spatial estimates. The general single-flow length-growth question remains open.

## Verification

The proof above is analytic. No Lean verification of the weak-limit argument or of (1) is claimed. The input pointwise estimate and high-record selection were already checked in the independent LengthGrowth project. The faster-scale oscillator limit and its infinite energy alone do not supply the profile budget (4).

The stress inequality and the existence of increasing record slices used in this argument are in the physical LengthGrowth project. [Physical arclength stress](../../LengthGrowth/ActualFlow/ArclengthCoercivity.lean) · [Record selection](../../LengthGrowth/ActualFlow/RecordSelection.lean)
