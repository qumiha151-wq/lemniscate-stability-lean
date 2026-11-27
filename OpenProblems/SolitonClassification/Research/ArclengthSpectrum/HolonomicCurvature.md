# Periodic curvature satisfying a polynomial-coefficient linear ODE

Let $X$ be a smooth closed plane free-elastic similarity profile with arclength period $P>0$ and signed curvature $k$. Suppose there are complex polynomials $p_0,\ldots,p_r$, at least one nonzero, with
$$
\sum_{j=0}^r p_j(s) k^{(j)}(s)=0 .
$$
Then $X$ is a circle, possibly traversed several times. Clearing denominators gives the same conclusion for rational coefficients. Analyticity of the similarity-profile system extends an identity on a nonempty real open interval to the entire real arclength axis. The Lean theorem on the linear relation takes the identity on this full axis.

## The linear equation forces finite Fourier support

Fix a real $s$. The polynomial $q_s(z)=\sum_j p_j(z)k^{(j)}(s)$ vanishes at $s+nP$ for every natural $n$, by periodicity of every derivative. Thus $q_s$ vanishes identically. Choose $z_0$ at which some nonzero $p_j$ does not vanish. The curvature satisfies the constant-coefficient equation with characteristic polynomial $A(v)=\sum_j p_j(z_0)v^j\ne0$. Integrating by parts on the closed period gives
$$
A(2\pi i n/P)\widehat k(n)=0\qquad(n\in\mathbb Z).
$$
Only finitely many integers can map to roots of $A$. Fourier inversion for a continuous function with summable coefficients identifies $k$ everywhere with its finite Fourier sum.

## The geometric equation rules out nonconstant finite Fourier sums

Write $T,N$ for the unit tangent and the counterclockwise unit normal. Put $G=aX+bJX+c$ for the similarity generator, $F=k''+k^3/2=-G\cdot N$, and $q=G\cdot T$. Differentiating the Frenet frame gives $F'=kq-b$ and $q'=a-kF$. Eliminating $q$ without division gives
$$
kk''''-k'k'''+\tfrac32 k^2(k')^2+\tfrac52 k^3 k''+\tfrac12 k^6-ak^2-bk'=0 .
$$
If $k$ has a highest positive Fourier frequency $N$, the coefficient of frequency $6N$ in the equation is $\widehat k(N)^6/2$. Every other summand has highest frequency at most $4N$. Hence the coefficient at $N$ must vanish. Since $k$ is real, excluding positive frequencies also excludes negative ones. A regular closed plane immersion has nonzero curvature if its curvature is constant. Integrating its Frenet system gives a covered circle.

The argument allows all similarity coefficients and all energy levels. A general real-analytic periodic curvature can have infinitely many Fourier coefficients, so the polynomial-coefficient hypothesis limits the scope of this classification.

