# A closed-curve angle equation and a posteriori test for strict separation

For a closed plane free elastic flow, strict separation of two entire time slices by a line is sufficient for the entire-curve migration in the question of [Miura and Wheeler](https://arxiv.org/abs/2404.12619). We derive a test from a finite spectral trajectory and finite height samples. We also enclose a smooth, nonround, genuinely closed trajectory over a short positive time. The example checks the evolution and error estimates. Its central symmetry keeps its centre fixed.

## Normalized equation and position

Use a $2\pi$-periodic coordinate $x$, with $ds=\rho\,dx$, $\rho=L/(2\pi)>0$, and physical time $dt=\rho^4 d\tau$. Represent the unit tangent by $T=(\cos\theta,\sin\theta)$ with $\theta=mx+\phi$ and $\phi$ periodic, $m\in\mathbb Z$. Put $N=JT$, $v=\theta_x$, $w=v_x$, $f=w_x+v^3/2$. The equiarclength velocity is $X_\tau=\rho(uT-fN)$. Differentiation in $x$, and comparison with $(\rho T)_\tau$, give
\[
 A=\langle vf\rangle,\qquad \rho_\tau=\rho A,\qquad u_x=A-vf,\qquad
 \theta_\tau=-f_x+uv .
\]
Here brackets denote the spatial mean. Starting from a smooth geometric solution, uniform arclength coordinates exist at each time by integration and inversion of its positive speed. The remaining time-dependent shift of $x$ can be chosen by a scalar ordinary differential equation so that $\langle u\rangle=0$. Let $D$ divide nonzero Fourier modes by $in$ and annihilate the constant mode. Integration by parts yields the closed equations
\[
 A=-\langle w^2\rangle+\tfrac12\langle v^4\rangle,\quad
 u=-vw+D(w^2-v^4/2),\quad
 \phi_\tau=-\partial_x^4\phi+N(v,w),\quad
 N(v,w)=-\tfrac52 v^2w+vD(w^2-v^4/2).
\]
The two meanings of $N$ are distinguished by its arguments in the nonlinear expression.

The coordinate displacement $\int_0^{2\pi}\rho T\,dx$ is conserved since $(\rho T)_\tau=(\rho(uT-fN))_x$. Initial closure therefore gives closure at all later times. Conversely, prescribe the anchor velocity at $x=0$ and integrate $\rho T$ in $x$. The reconstructed curve has exactly the prescribed velocity, speed $\rho$, signed curvature $v/\rho$ and elastic force $f/\rho^3$. In physical time its normal velocity is the negative elastic force. These identities use the geometric definitions of the Migration project. The periodic primitive $v^2T/2+wN$ has derivative $fN$. Thus the mean coordinate $C=\langle X\rangle$ satisfies $C_\tau=\rho\langle uT\rangle$. This equation needs at most second spatial derivatives of the angle.

## Spectral enclosure

For periodic Fourier series put $\|z\|_A=\sum_n |z_n|$ and $\|z\|_X=\sum_n(1+n^2)|z_n|$. Convolution gives the algebra inequality in $A$, $D$ is a contraction there, and the first and second derivative errors are bounded by $e/2$ and $e$ when the angle error in $X$ is at most $e$. Constants in $v$ include the winding $m$. If each of two states has $\|v\|_A\le V$, $\|w\|_A\le W$, expansion of products gives
\[
 \|\delta N\|_A\le(5VW+W^2+\tfrac52 V^4)\|\delta v\|_A+
                    (\tfrac52V^2+2VW)\|\delta w\|_A.
\]
Set $K=(5VW+W^2+5V^4/2)/2+5V^2/2+2VW$. For a reference $\hat\phi$ on $0\le \tau\le h$ and proposed radius $r$, take $V=\sup\|\hat v\|_A+r/2$, $W=\sup\|\hat w\|_A+r$. Let $R$ bound the unweighted norm of $\hat\phi_\tau+\partial_x^4\hat\phi-N(\hat v,\hat w)$, and $E_0$ bound the initial $X$-error. A sufficient condition for the exact angle to have error strictly less than $r$ throughout is
\[
                 E_0+(h+\sqrt{2h})(R+Kr)<r.                 \tag{1}
\]
Indeed each Fourier mode solves a scalar variation-of-constants equation. The multiplier $(1+n^2)e^{-s n^4}$ is bounded by $1+1/\sqrt{2s}$ for $s>0$, since $e^{2sn^4}\ge 2sn^4$. The free semigroup contracts in $X$. Summing the forced mode bounds and integrating in time gives (1) on any preceding interval where the error is at most $r$. Continuity and first contact rule out equality. Alternatively the associated Duhamel map sends the closed error ball in $C([0,h];X)$ into itself with Lipschitz constant at most $(h+\sqrt{2h})K<1$. Continuity follows from strong continuity of the diagonal semigroup and the integrable smoothing bound. For smooth closed initial data the genuine geometric solution is smooth and unique. It agrees while defined with the mild Fourier solution in this gauge by the same local contraction. On a bounded certified slab $V,W$ bound $A$, hence $\rho$ stays between positive finite constants. If normalized time stopped before $h$, the physical time would remain finite and global smooth existence and positive speed would extend the chart. This identifies the enclosure with the genuine closed flow.

For a polynomial reference in time with trigonometric-polynomial coefficients, ordinary untruncated Fourier convolution gives the full residual. If the largest mode is $M$, the quintic term can reach $5M$. No spatial grid evaluation can replace checking the unresolved higher modes without a separate aliasing bound. In the example below the coefficientwise sum of absolute real and imaginary parts over all time powers in $\tau/h\in[0,1]$ suffices.

## Recovering a strict separation with finite errors

For any unit projection let $T_e$ be the projected tangent. Suppose the angle error is at most $r$. The scalar scale equation implies $|A-\hat A|\le 2Wr+V^3 r$: subtract the squares and fourth powers using the two derivative error bounds. Integrate this with the error in $(\log\hat\rho)'$ to bound $|\log\rho-\log\hat\rho|$. Denote resulting pointwise bounds for $|\rho-\hat\rho|$ and $\hat\rho$ by $d$ and $H$, respectively. The projected-slope error is at most $d+Hr$ before any correction for approximate closure. The drift velocity obeys
\[
 U=VW+W^2+V^4/2,\qquad
 B_u=(W+2V^3)r/2+(V+2W)r,\qquad
 |C'_e-\hat\rho\langle\hat u\hat T_e\rangle|\le dU+H(B_u+Ur).
\]
These estimates use $\|u\|_\infty,\|\hat u\|_\infty\le U$ and $|T_e-\hat T_e|\le|\theta-\hat\theta|$. Initial-mean error, integrated velocity error, and any residual of the approximate mean equation give a bound $m_i$ at each of the two slices. Integration and exponentiation in these scalar estimates require verified bounds in a numerical application.

Use a periodic reconstructed comparison height $Z_i$. If the reference projected slope has a small nonzero mean, subtract that mean before spatial integration, and add its absolute value to the slope error. Fix the constant term to the verified approximate height mean. Let $e_i$ bound the true slope error. For any periodic error $g$ of period $P>0$ one has
\[
       |g(x)-\langle g\rangle|\le P\|g'\|_\infty/4.
\]
Indeed pair the points $x-s,x+s$ for $0\le s\le P/2$ and integrate the derivative bound. On a uniform grid with $n$ cells, any point lies within $P/(2n)$ of a sampled point. If $v_i$ bounds the absolute slope of the true height (one may use $\rho_i$), its deviation from the reference height at that sample is at most
\[
                 b_i=m_i+Pe_i/4+Pv_i/(2n).
\]
Consequently $\min_j Z_1(jP/n)-\max_j Z_0(jP/n)>b_0+b_1$ places the two **entire** true curves on opposite sides of a separating line. Errors in evaluating the reference samples must be included in their enclosures. Rotation of the plane turns the separating line horizontal. A nonpositive lower bound gives no such example.

## Exact short-slab calculation

Take $\rho(0)=1$ and $\theta(0,x)=x+\sin(2x)/10$. The half-period adds $\pi$ to the angle, so the integral of each tangent projection is zero. The signed force at $x=0$ differs from that at $x=\pi/4$. Put $h=10^{-6}$ and choose the first-order reference $\hat\phi=\phi(0)+\tau[-\partial_x^4\phi(0)+N(v(0),w(0))]$. The initial derivative has largest mode ten. The [rational calculation](spectral_example.py) evaluates 170 nonzero residual coefficients through spatial mode 50 and time degree five. Every coefficient of time degree zero cancels. For $r=7\cdot10^{-8}$ it certifies
\[
 R\le 47091/10^9,\qquad K\le 8432071/10^6,\qquad
 (h+\sqrt{2h})(R+Kr)\le 67489/10^{12}<r.
\]
The calculation uses exact rational real and imaginary parts, including the bound $\sqrt{2h}\le1/707$. All figures concern this short slab in normalized time. They do not enclose any later numerical candidate.

For a time-dependent Fourier forcing with summable envelopes $b_n=\sup_s |f_n(s)|$, each genuine scalar coefficient satisfying $z'_n=-n^4z_n+f_n$ obeys the sharper bound $(1+n^2)|z_n(t)|\le(1+n^2)|z_n(0)|+(t+\sqrt{t/2})b_n$. The integrating factor gives the exact kernel. For $y\ge0$, differentiating $y-2(1-e^{-y})^2$ gives $(1-2e^{-y})^2\ge0$. This bounds the smoothing contribution of each integrated mode by $\sqrt{t/2}$. Taking each mode's supremum and then summing gives the stated improvement for the stronger forcing norm. It does not require interchanging a supremum with an infinite sum.

The Lean modules check the geometric reconstruction, actual force, mean drift, both full parameter ranges in the separation test, first-order Fourier coefficients of the closed example, coefficient arithmetic through mode 50, the algebra norm and both smoothing bounds. The independent kernel calculation uses rounded scalar bounds to obtain $67490/10^{12}<7\cdot10^{-8}$; the standalone exact-arithmetic program above retains the unrounded intermediate bounds. The weighted Fourier function-space construction and its application to smooth global solutions are written proofs. A migrating example still requires a closed initial curve with a strictly positive verified separation.
