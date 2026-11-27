# A meromorphic continuation of the actual Bernoulli curvature

For the Bernoulli curve \(\beta(u)=\sin u/(1+i\cos u)\) let \(\ell\) be its arclength from \(u=0\) and let \(\theta=\ell^{-1}\). Its normalized curvature
\[
  w(s)=\frac{k(s)}3
       =\frac{\sin\theta(s)}{\sqrt{1+\cos^2\theta(s)}}
\]
satisfies \(w(0)=0,\ w'(0)=1,\ w''=-2w^3\). The first integral is \((w')^2+w^4=1\), and \(P=\ell(2\pi)>0\) is a real period. These data determine a single-valued meromorphic continuation with periods \(P\) and \(iP\).

Near zero, choose the analytic branch \(q(\xi)=\sqrt{1-\xi^4}\) with \(q(0)=1\). The primitive of \(1/q\) vanishing at zero has derivative 1 there. Its local analytic inverse \(u\), together with \(v=q(u)\), therefore solves \(u'=v,\ v'=-2u^3\) with initial state \((0,1)\). Uniqueness along the real axis identifies this analytic germ with the actual \(w,w'\). The pair \((u(iz),v(iz))\) agrees near zero with \((iu(z),v(z))\). Restriction to a real interval gives identical initial-value problems over the complex state space, and the holomorphic identity theorem gives equality of the germs.

Define the rational duplication map on pairs by
\[
 D(x,y)=\left(\frac{2xy}{1+x^4},\frac{1-6x^4+x^8}{(1+x^4)^2}\right).
\]
If \(x'=y,\ y'=-2x^3,\ y^2+x^4=1\), differentiation gives \(D_1'=2D_2\) and \(D_2'=-4D_1^3\). On the entire real axis the denominator is at least 1. Uniqueness with initial value \((0,1)\) yields \(D(w(s),w'(s))=(w(2s),w'(2s))\). Hence the analogous local identity holds for \((u,v)\) by analytic continuation.

For complex \(z\) choose \(n\) large enough to place \(z/2^n\) in the initial disk and set
\[
 (W(z),V(z))=D^{\,n}\big(u(z/2^n),v(z/2^n)\big).
\]
Increasing \(n\) gives the same pair by the local doubling identity. On every neighborhood small enough to use a fixed \(n\), these are meromorphic functions, by finite rational composition of the initial analytic pair. On the real axis every intermediate state is the actual real oscillator state at a doubled parameter, so the extension is holomorphic there and agrees with \(w\).

The map \(D\) commutes with \((x,y)\mapsto(ix,y)\), giving \(W(iz)=iW(z)\). The real period \(P\) extends by the meromorphic identity theorem. Consequently \(W(z+iP)=W(z)\) as meromorphic germs, and filling removable values gives a representative with both ordinary periods. The argument survives arbitrary real arclength shifts and positive spatial dilations. It applies to the physical curvature \(3w\) and to the scaled and shifted curvatures of the closed oscillator profiles.
