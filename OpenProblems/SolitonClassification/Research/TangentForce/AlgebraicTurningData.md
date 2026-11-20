# Algebraic turning data and evolutes of closed elastic similarity profiles

Let \(X\) be a smooth closed planar free-elastic similarity profile, with oriented unit tangent \(T=(\cos\theta,\sin\theta)\), left normal \(N\), signed curvature \(k\) and elastic force \(F=k_{ss}+k^3/2\). Put \(w=T_x+iT_y\). Each of the following conditions, on just one real open arc, implies that the profile is a circle or Bernoulli's lemniscate, up to similarity and multiple covering.

1. A nonzero polynomial \(P\in\mathbb C[W,Y]\) satisfies \(P(w,F)=0\).
2. A nonzero polynomial \(P\in\mathbb C[W,Y]\) satisfies \(P(w,k)=0\).
3. On an arc with \(k\ne0\), the evolute \(X+N/k\) lies in the zero set of a nonzero plane polynomial.

Conversely, all three conditions hold for the circle and Bernoulli's lemniscate. Using \(w\) as the tangent variable excludes the tautological relation \(T_x^2+T_y^2=1\). The statements allow multiple values over one tangent direction.

## Force and curvature in the tangent parameter

Take the expansion centre as origin. The real dilation and angular coefficients are \(a>0,b\), and
\[
p=X\cdot N,\quad q=X\cdot T,\quad F=-ap-bq,\quad H=aq-bp.
\]
The support equations give \(F_s=kH-b\) and \(H_s=a-kF\). The profile equations are analytic. A nonconstant profile has an arc with \(k\ne0\) inside every nonempty open interval. Work there, write \(u=1/k\), and let a dot denote \(d/d\theta=iw\,d/dw\). Thus
\[
\dot F=H-bu,\qquad \dot H=au-F,\qquad
F u^5=-u\ddot u+3\dot u^2+\tfrac12 u^2. \tag{1}
\]
The last formula follows by applying \(\partial_s=u^{-1}\partial_\theta\) twice to \(k=u^{-1}\). Differentiation with respect to \(\theta\) preserves the field of algebraic germs over \(\mathbb C(w)\) in characteristic zero. Since \(w\) is nonconstant on the chosen arc, a nontrivial relation in condition 1 makes \(F\) algebraic over that field's base.

If \(b=0\), (1) gives \(u=(F+\ddot F)/a\). If \(b\ne0\), put \(\lambda=a/b\), \(g=-(F+\ddot F)/b\). Then \(\dot u=\lambda u+g\), with \(g,\dot g\) algebraic. Eliminating \(\dot u,\ddot u\) in (1) gives
\[
F u^5=(2\lambda^2+\tfrac12)u^2+(5\lambda g-\dot g)u+3g^2. \tag{2}
\]
The polynomial in \(u\) is nonzero as a polynomial over the algebraic germs: the coefficient \(2\lambda^2+1/2\) is strictly positive for real \(\lambda\). Thus \(u\) is algebraic in both cases. Condition 2 gives this conclusion directly.

In either case \(k,v=k_s,F,H=\dot F+bu\) are all algebraic over \(\mathbb C(w)\), by (1) and differentiation. The invertible linear equations defining \(F,H\) show that \(p,q\) are algebraic as well. Both components of \(X=qT+pN\) therefore lie in a common finite extension of \(\mathbb C(w)\). They are algebraically dependent, so the plane-image classification applies. [Algebraic plane classification](../ReflectedExpanders/AlgebraicPlaneClassification.md)

## The evolute

For \(Y=X+uN\), the Frenet equations give \(\dot Y=\dot u N\). A constant evolute on an arc implies constant \(u\) there and hence constant curvature on the entire analytic profile. Otherwise restrict to an arc where \(k\dot u\ne0\) and \(Y\) is a regular point of an irreducible plane algebraic curve. In axes where its first coordinate is a local parameter \(y\), its second coordinate and its slope are algebraic over \(\mathbb C(y)\). Its unit tangent, up to a fixed choice of sign, is \(N\) and is algebraic over the same field. In particular \(w\) is algebraic over \(\mathbb C(y)\). It is nonconstant because \(k\ne0\). The common function field has transcendence degree one, so the components of \(Y\) are in turn algebraic over \(\mathbb C(w)\).

Now \(\dot u=\dot Y\cdot N\) and \(\ddot u\) are algebraic over \(\mathbb C(w)\). The support equation reads \(F=au+B\), where \(B=-aY\cdot N-bY\cdot T\) is algebraic. Substitution into the last equation of (1) produces a polynomial in \(u\) with leading term \(au^6\) and algebraic coefficients. Since \(a>0\), \(u\) is algebraic. Hence \(X=Y-uN\) has algebraically dependent coordinates, and the plane-image classification applies here as well.

For the converse, take a regular arc of either algebraic profile with nonzero curvature. Both tangent components, the curvature, its arclength derivatives and the evolute components are algebraic over a local Cartesian coordinate. This follows by implicit differentiation and adjoining the square root for unit speed. Passing to the nonconstant tangent coordinate \(w\) again uses transcendence degree one. A constant evolute, as on a circle, satisfies condition 3 directly.

This is a mathematical proof. The separate Lean theorem on a globally single-valued force as a function of the oriented tangent permits arbitrary functions and classifies that subclass as circles alone.
