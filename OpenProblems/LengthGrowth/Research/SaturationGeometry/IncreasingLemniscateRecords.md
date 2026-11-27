# Divergent nodal charge on one strictly increasing, bounded record trajectory

There exists a smooth non-self-similar primitive closed planar free elastic flow, of turning number zero, on which $U(t)=E(t)L(t)$ increases strictly for all $t\ge0$ and tends to the finite product $U_*$ of the expanding Bernoulli lemniscate. For every $H<U_*$ its positive nodal charge on increasing records above $H$ has infinite integral. More precisely, for $F=k_{ss}+k^3/2$, $D=\int F^2ds$ and $B=\sum_{k=0}|k_s|$ during one traversal,
\[
 2\sqrt{L(t)D(t)}\,B(t) \sim \frac{12\sqrt{L_\beta D_\beta}}{30t}.
\]
Here $\beta$ is the once-covered reference lemniscate in the scale used below. Nevertheless $L(t)\asymp t^{1/4}$, $E(t)\asymp t^{-1/4}$, and the actual integrated increase of $U$ is finite. This supplies an obstruction to estimating the full positive nodal term by energy dissipation even on the set of strict records. The threshold $H=U_*$ makes that set empty. The example does not disprove fourth-root growth or the criterion which permits a threshold above the limiting product.

## A real mode detected by the scale-invariant energy

Work in the physical convention $X_t^\perp=-F N$. Use the graph equation over $\beta$ for the normalized time $\tau=(1/30)\log(1+30t/a^4)$ and spatial factor $\rho=(a^4+30t)^{1/4}$. The normalized normal velocity is $-(F+(15/2)X\cdot N)N$. On the reference curve, write $x=\sqrt2s$, $k=3q$, $X\cdot N=-q^3$, and choose the origin at $q(0)=1$. Then
\[
 q_{xx}=-q^3,\qquad q_x^2=(1-q^4)/2.
\]
The function $q$ is even and changes sign under translation by half its least period. For the normal graph $X=\beta+fN_\beta$ the derivative $A$ of its normalized velocity and the ordinary $L^2(dx)$ adjoint are
\[
 A=-4\partial_x^4-45q^2\partial_x^2-75qq_x\partial_x-69/2-(45/2)q^4,
 \qquad A^*=-4\partial_x^4-45q^2\partial_x^2-105qq_x\partial_x-42.
\]
For the explicit Bernoulli curve, the formulas for $q$, $X\cdot N$ and $X\cdot T=\sqrt2qq_x$ follow by arclength differentiation of its parametrization. [Edwards et al., Proposition 13](https://arxiv.org/abs/1505.02978) · [Miura and Wheeler, free elastic flow and the expanding Bernoulli curve](https://arxiv.org/abs/2404.12619)

The displayed operator also follows by direct variation. Write $h=X\cdot N$, $b_0=X\cdot T$ and $V=vN$. Then $\delta k=v_{ss}+k^2v$, $\delta\partial_s=kv\partial_s$, and $\delta h=v-b_0v_s$. Consequently the negative of $A$ in the $s$ coordinate is
\[
 \partial_s^4+(5/2)k^2\partial_s^2+(5kk_s-(15/2)b_0)\partial_s
       +3k_s^2+4kk_{ss}+(3/2)k^4+15/2.
\]
Inserting $k=3q$ and changing variables gives $A$ above. Its adjoint follows by periodic integration by parts and $(q^2)_{xx}=1-3q^4$. The graph-to-normal velocity factor equals one at zero and its derivative multiplies the zero stationary normalized speed there. These computations reproduce the graph linearization in the section *Normalization and the graph equation* of the supplied stability manuscript.

The derivative of $U$ on a height $v$ is $\int g v\,ds$, where the ordinary first variations of $E,L$ give
\[
          g=L_\beta[(15/2)q^3-3(E_\beta/L_\beta)q].                 \tag{1}
\]
Both $g$ and all its adjoint iterates belong to the real sector of even functions which are antiperiodic under a half-period translation. Both $A$ and $A^*$ preserve its complexification. The two norms $L^2(ds)$ and $L^2(dx)$ differ by a fixed factor. For positive integer $j$,
\[
(q^j)_{xx}=\tfrac12 j(j-1)q^{j-2}-\tfrac12 j(j+1)q^{j+2}.
\]
Consequently $A^* q^j$ is a polynomial of degree at most $j+4$, whose coefficient of $q^{j+4}$ equals
\[
 j\left[-(j+1)(j+2)(j+3)+\tfrac{45}2(j+1)+\tfrac{105}2\right].
\]
It is nonzero at $j=3$ and strictly negative for $j\ge7$. The polynomials $(A^*)^j g$ have degrees exactly $3+4j$ and are linearly independent, since $q$ covers an interval. In particular $g$ cannot belong to a finite-dimensional invariant adjoint spectral subspace.

Here is a direct completeness argument adequate for this observation. On this sector let $P=-4\partial_x^4$, $C=A-P$, and let $b$ be $2\pi$ divided by the $x$-period. The eigenvalues of $P$ are the simple numbers $-r_n=-4b^4 n^4$ for positive odd $n$, with cosine eigenvectors. $C:H^2\to L^2$ is bounded. On the circles $|z|=R_n=(r_n+r_{n+2})/2$,
\[
 \|(z-P)^{-1}\|_{L^2\to L^2}\le C_0 n^{-3},\qquad
 \|C(z-P)^{-1}\|_{L^2\to L^2}\le C_0/n .                       \tag{2}
\]
Indeed $|z+r_j|\ge|R_n-r_j|$, so the second bound follows by bounding $(1+j^2)/|R_n-r_j|$ separately at $j<n/2$, $n/2\le j\le2n$ and $j>2n$. The Neumann series for $P+uC$, $0\le u\le1$, gives invertibility on every sufficiently large circle. Continuous deformation of the Riesz projections preserves their finite ranks. Between two successive such circles there is exactly one eigenvalue of $A$ counted algebraically. It is simple and real because the real operator has conjugate nonreal eigenvalues. It is negative for all large $n$ (the same Neumann estimate on the positive real axis excludes arbitrarily large positive spectrum).

If $f\in H^2$, the resolvent identity bounds $\|[(z-A)^{-1}-(z-P)^{-1}]f\|_2\le C_1 n^{-6}\|f\|_{H^2}$ on these circles. In fact the $A$ resolvent contributes $O(n^{-3})$, and $\|(z-P)^{-1}f\|_{H^2}\le C_0n^{-3}\|f\|_{H^2}$. Integration on a circle of length $O(n^4)$ proves that the enclosed Riesz projection of $A$ tends to the identity on $H^2$ in $L^2$. If $g$ annihilated all sufficiently high real eigenspaces, only one fixed finite-dimensional low projection could contribute to $\langle g,f\rangle$. Density of $H^2$ in $L^2$ would put $g$ in the range of the adjoint of that low projection, contradicting the polynomial calculation. There is therefore a smooth real eigenvector $v$ of the full periodic operator with eigenvalue $\lambda<0$ and $c_v=\int gv\,ds\ne0$. This argument in fact finds infinitely many distinct visible eigenvalues. Only the linear part of the proof uses the symmetry sector.

## Realizing the selected mode on one exact trajectory

Write $\mathcal F(f)=Af+Q(f)$ for the full, unmodulated normalized graph equation over the once-covered reference. We construct a solution with the asymptotic expansion $f=\epsilon e^{\lambda\tau}v+w$, where the error decays faster than the first term. Prescribing the faster decay also fixes the limiting rotational component. Work on the full real periodic space, without assuming nonlinear invariance of a Fourier sector.

Take $-\lambda<\mu<-2\lambda$ with no spectrum on $\operatorname{Re} z=-\mu$. Such a choice exists because $A$ is an elliptic sectorial operator with compact resolvent. On the base space $H^4$ its domain is $H^8$ and its spectral projections agree on smooth functions with the $L^2$ projections, by elliptic regularity. Split the spectrum to the left and right of this line. The right part is finite dimensional. The linear map $w' -Aw=h$ has a bounded right inverse from $e^{-\mu\tau}L^2(H^4)$ into the normed space
\[
 e^{\mu\tau}w\in H^1(\mathbb R_+;H^4)\cap L^2(\mathbb R_+;H^8),
 \qquad \sup_{\tau\ge0} e^{\mu\tau}\|w(\tau)\|_{H^6}<\infty .
\]
On the fast subspace take zero initial value and use Hilbert-space maximal regularity for the exponentially stable generator $A+\mu$. Equivalently, extend the weighted forcing by zero before time zero and use Plancherel on the causal convolution: the Fourier multipliers $i\xi(i\xi-A-\mu)^{-1}$ and $(A+\mu)(i\xi-A-\mu)^{-1}$ are uniformly bounded by sectoriality and the spectral gap. The time trace is $H^6$. On the slow finite-dimensional subspace use $-\int_\tau^\infty e^{(\tau-r)A} h(r)\,dr$; the weighted kernel is exponentially decreasing in $r-\tau$, with possible polynomial Jordan factors. These real linear maps preserve real functions. [De Simon, Hilbert-space maximal regularity, Theorem 4.4](https://www.numdam.org/item/RSMUP_1964__34__205_0.pdf) · [Prüss, Simonett and Zacher, Section 2](https://arxiv.org/abs/0807.1539)

In a small $H^6$ ball, the local fourth-order graph formula gives the bound
\[
 \|Q(u)-Q(v_0)\|_{H^4}\le C\big[(\|u\|_{H^6}+\|v_0\|_{H^6})\|u-v_0\|_{H^8}
 +(\|u\|_{H^8}+\|v_0\|_{H^8})\|u-v_0\|_{H^6}\big].
\]
This follows by differentiating the graph formula through four spatial orders. Its leading coefficient depends smoothly on $u,u_s$, and the remaining monomials in $u_{ss},u_{sss}$ have degree at most three. Terms linear at zero have been subtracted; the one-dimensional Sobolev product estimates put the top derivative in $L^2$ and the lower factors in $L^\infty$. The corresponding pointwise estimate $\|Q(u)\|_{H^2}\le C\|u\|_{H^6}^2$ follows by two differentiations. Apply the right inverse to $Q(\epsilon e^{\lambda\tau}v+w)$. Its value at zero is $O(\epsilon^2)$ in the weighted solution space because $\mu+2\lambda<0$. Placing low factors in the trace supremum and high factors in weighted $L^2$ bounds its Lipschitz constant on a ball of radius $K\epsilon^2$ by $C(|\epsilon|+K\epsilon^2)$. A contraction on that ball gives an actual real solution. The equation $w'=Aw+Q(f)$ then yields
\[
 \|w(\tau)\|_{H^6}+\|w'(\tau)\|_{H^2}=O(\epsilon^2e^{-\mu\tau}).
\]
Here the $H^6$ trace is continuous and the equation makes the $H^2$ time derivative continuous. Positive-time parabolic smoothing gives a smooth immersion; restricting to any positive starting time gives smooth initial data as well. Undoing the normalization and changing material labels to remove tangential velocity gives a true free elastic flow. The curve has turning number zero by proximity to $\beta$. It is primitive on a sufficiently late tail: choose one embedded reference subarc whose interior contains a point visited only once by $\beta$. On a smaller arc the immersion remains graphical under small $C^1$ perturbation, and a closed complement separated from that point stays disjoint from a small ball around it. The perturbed curve therefore has a point visited exactly once, excluding any multiple cover.

Since $U$ is smooth in normal graph coordinates on $H^2$, Taylor expansion and (1) give
\[
 U(\tau)=U_*+\epsilon c_v e^{\lambda\tau}+O(\epsilon^2 e^{-\mu\tau}),\qquad
 U_\tau(\tau)=\epsilon\lambda c_v e^{\lambda\tau}+O(\epsilon^2 e^{-\mu\tau}).
\]
Choose $\epsilon c_v<0$. Both strict increase and $U<U_*$ hold for every sufficiently late normalized time. Restart the physical trajectory at such a time. Its entire future consists of increasing records when records are taken from that initial time. The strict change of the similarity-invariant quantity $U$ also excludes every exact self-similar motion.

## The unspent cancellation at these records

In the normalized graph the two curvature zeros of $\beta$ are simple and $|k_s|=3$ at each. Convergence in $H^6$ gives exactly two such zeros on the tail, with $\widehat B\to6$, $\widehat D\to D_\beta>0$ and $\widehat L\to L_\beta$. In the original geometry $L=\rho\widehat L$, $D=\rho^{-5}\widehat D$, $B=\rho^{-2}\widehat B$ and $dt=\rho^4 d\tau$. Thus $2\sqrt{LD}B\,dt=2\sqrt{\widehat L\widehat D}\widehat B\,d\tau$ with a strictly positive limit in normalized time. The indicated physical $t^{-1}$ asymptotic holds after any finite restart as well. Meanwhile $D$ is integrable and $U_\tau$ is exponentially integrable. The signed deficits in the nodal identity cancel the nonintegrable leading positive term on this single strictly increasing trajectory.

This is a written mathematical proof. It uses the supplied graph linearization and standard parabolic maximal regularity and adds no Lean theorem. It leaves open whether one trajectory can have unbounded $U$.
