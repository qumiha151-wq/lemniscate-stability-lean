# Linear order is optimal for invariant turning-dependent curvature-oscillation sublevels

There are constants \(C>0\) and \(m_0\) such that for **every** integer \(m\ge m_0\) and every real \(K\ge C m\), there is a smooth closed immersed plane curve of turning number \(m\) whose initial curvature oscillation equals \(K\) and whose curvature oscillation has strictly positive initial derivative under free elastic flow. Reversing orientation gives the negative turning cases. Consequently a family of invariant closed sublevels \(\{L\int k^2ds-(2\pi m)^2\le W(m)\}\) cannot have superlinear thresholds along any sequence \(m\to\infty\). The lower bound proved in the companion article has linear width. The two conclusions determine the order of the largest universally invariant sublevel up to universal multiplicative constants. The upper constant below is existential.

## A local curvature block with an outward rate

Write \(F=k''+k^3/2\) in physical arclength, \(B=\int k^2,\ E=B/2,\ D=\int F^2,\ J=\int kF\). A free elastic flow satisfies \(L'=J,\ E'=-D\) and keeps its signed turning fixed. Thus \((EL)'=EJ-LD\). Take the periodic curvature function
\[
q(s)=\tfrac32\cos(3s/4),\qquad H=q''+q^3/2.
\]
The period is \(8\pi/3\). In the angle \(x=3s/4\) one has
\[
H(s)=\tfrac{27}{64}(\cos x+\cos 3x).
\]
The averages of \(q,\ q^2,\ qH,\ H^2\) over a period are respectively
\[
0,\qquad b_0=\tfrac98,\qquad j_0=\tfrac{81}{256},\qquad d_0=\tfrac{729}{4096}.
\]
The two exact identities needed here are \(2b_0 j_0-4d_0=0\) and \(2j_0-4d_0+b_0-1=47/1024>0\).

Fix a smooth cutoff \(\chi\colon\mathbb R\to[0,1]\) equal to zero on \((-\infty,1/4]\) and to one on \([3/4,\infty)\). For \(u\ge1\) define a block of length \(\ell=u+2\) by
\[
k_u(s)=1+\chi(s)\chi(u+2-s)(q(s)-1),\qquad 0\le s\le u+2.
\]
This is identically 1 near both ends and agrees with \(q\) on \([1,u+1]\). Write \(\alpha=\int k_u,\ b=\int k_u^2,\ j=\int k_u F_u,\ d=\int F_u^2\) over the block. The four functions are continuous in \(u\) by smooth dependence and variable-limit integration. There is one fixed \(K_0\) such that, uniformly for \(u\ge1\),
\[
|\alpha|,\quad |b-b_0u|,\quad |j-j_0u|,\quad |d-d_0u|\le K_0.
\]
Indeed, each zero-mean difference on the middle interval has a bounded periodic primitive. Each of the two end intervals has length one and all derivatives of the displayed curvature through order two are uniformly bounded there. Such bounds are independent of the phase of \(q\) at the moving end.

## Exact closure and the outward sign

Let \(p\le m\) be the greatest odd integer at most \(m\). Traverse one block and a circular arc of curvature 1 of length \(\pi p-\alpha\). For all sufficiently large \(m\) this length is positive, uniformly in \(u\). Take a second identical block and a circular arc of length \(\pi p-\alpha+2\pi(m-p)\). The first half turns its tangent by \(\pi p\), so the second half starts with the opposite tangent. The part of the second half that repeats the first has exactly the opposite displacement. Its extra integer full circles contribute zero displacement. The final tangent matches the initial tangent, and all seams lie in open pieces of curvature 1. Equivalently the explicit unit-speed immersion is \(\gamma(s)=\int_0^s\exp(i\int_0^v k(w)dw)dv\) glued periodically. It is a smooth closed immersion of turning number \(m\).

Put \(T=\pi m-\alpha\), so the total arclength of the circular pieces is \(2T\). The actual integral formulas are
\[
 L=2(T+\ell),\quad E=T+b,\quad D=2(T/4+d),\quad J=2(T/2+j),\quad 2\pi m=2(T+\alpha).
\]
They give exactly
\[
 (EL)'=T(2j-4d+b-\ell)+2bj-4\ell d,\qquad
 \delta_m(u)=2EL-(2\pi m)^2
 =4\big[T(\ell+b-2\alpha)+\ell b-\alpha^2\big].
\]
The uniform block bounds and period identities imply
\[
 (EL)'=\pi m\,\frac{47}{1024}u+O(m+u+1),
\]
with a universal implied constant. The potentially quadratic \(u^2\) term cancels, so this estimate holds **uniformly without any comparison between \(u\) and \(m\)**. Hence there exist \(u_0,m_0\) such that \((EL)'>0\) for \(m\ge m_0,\ u\ge u_0\).

For fixed \(u=u_0\), \(\delta_m(u_0)\le Cm\) after increasing \(C\). For fixed \(m\ge m_0\), \(\delta_m(u)\to+\infty\) because \(\ell b=b_0u^2+O(u+1)\) and \(T\) is bounded in \(u\). Continuity supplies \(u\ge u_0\) with \(\delta_m(u)=K\) for each \(K\ge Cm\). At that curve \(\delta'(0)=2(EL)'>0\), so every actual smooth flow starting there immediately crosses the specified upper boundary. Smooth short-time existence for smooth closed immersed initial curves suffices for this conclusion. The assertion concerns initial-data sublevels, and leaves open the unrestricted upper growth law of each individual orbit.

## Uniform signed statement

The separate trigonometric construction gives an outward curve of every signed winding \(m\), including zero, on every exact level above an explicit quadratic threshold. On the finite range \(|m|<m_0\) this threshold is at most a constant times \(1+|m|\). For larger \(|m|\) apply the linear result above, reflecting the position across the real axis for negative turning. Reflection changes the signs of curvature and force, preserves length, energy, dissipation and length rate, and negates the signed turning integral. Thus a single universal \(C'>0\) suffices for **all** \(m\in\mathbb Z\) and \(K\ge C'(1+|m|)\).

The companion lower and upper theorems together imply that for all sufficiently large nonzero winding numbers the greatest possible universally invariant threshold, expressed as a supremum, lies between two positive universal multiples of \(|m|\). They do not identify the optimal constants. The upper counterexamples can have outward initial rate even though the length bound for each individual flow remains an open question in general.

Miura and Wheeler recall the global smooth existence theorem for closed immersed initial data and attribute it to Dziuk, Kuwert and Schätzle. [Miura and Wheeler, Introduction](https://arxiv.org/html/2404.12619v3) [Dziuk, Kuwert and Schätzle, *Evolution of Elastic Curves in ℝⁿ*](https://doi.org/10.1137/S0036141001383709)
