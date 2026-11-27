# Rational curvature in one arclength frequency

Let a smooth closed immersed plane curve be a free elastic similarity profile. Suppose its signed arclength curvature satisfies
\[
  k(s)=\frac{A(e^{i\omega s})}{B(e^{i\omega s})}
\]
for complex polynomials \(A,B\), a real frequency \(\omega\), and a denominator nonzero at every parameter value. Then there are \(K\in\mathbb R\setminus\{0\}\), \(O\in\mathbb C\) and \(Z\in\mathbb C\setminus\{0\}\) such that \(X(s)=O+Ze^{iKs}\). Both the energy and the rotation coefficient are unrestricted. Multiple traversals are allowed. This gives an elementary proof for part of the class considered in the [meromorphic arclength argument](../ReflectedExpanders/MeromorphicArclengthClassification.md).

For \(\omega=0\) the curvature is constant immediately. Otherwise write \(\mu=i\omega\) and \(D=\mu z\,d/dz\). Set \(f=A/B\) after cancellation of common factors. A closed similarity profile has a fixed similarity center and positive dilation coefficient \(a\). Write \(b\) for the angular coefficient, \(G=aX+bJX\), \(q=G\cdot T\) and \(F=k''+k^3/2\). From \(F=-G\cdot N\) follow \(q'=a-kF\) and \(kq=b+F'\). Differentiate the second identity, multiply by \(k\), and substitute both identities. The result along the physical curve is the vanishing of
\[
 S(f)=2(fD^4 f-Df\,D^3 f)+3 f^2(Df)^2+5 f^3D^2 f+f^6-2af^2-2bDf .
\]
The chain rule along the frequency circle identifies these iterates with arclength derivatives. Clearing denominators gives a polynomial that vanishes on infinitely many distinct points. Hence \(S(f)\) vanishes at every regular complex point.

At zero, \(D\) preserves the order of a pole. At a pole of order \(m>0\), the sextic term in \(S\) has order \(6m\), strictly higher than the orders of all other terms. Thus \(f\) is regular at zero. In the coordinate \(z^{-1}\), the Euler operator has the same form with coefficient \(-\mu\). The same argument at infinity gives \(\deg A\leq\deg B\).

At a nonzero finite pole \(\alpha\), differentiation raises the pole order by at most one. If \(m>1\), the orders of the quadratic and quartic differential terms are at most \(2m+4\) and \(4m+2\), both less than \(6m\). Every pole is therefore simple. For \(f(z)=v/(z-\alpha)+O(1)\), the coefficient of \((z-\alpha)^{-6}\) in \(S(f)\) is
\[
 v^2\bigl(v^2+4(\mu\alpha)^2\bigr)\bigl(v^2+9(\mu\alpha)^2\bigr).
\]
It follows that \(v/\alpha\in\{2\omega,-2\omega,3\omega,-3\omega\}\).

In partial fractions write \(f(z)=d+\sum_\alpha r_\alpha\,\alpha/(z-\alpha)\), with all \(r_\alpha\) real. For each pole, the terms \(\alpha/(e^{i\theta}-\alpha)\) at angles \(\arg\alpha+v\) and \(\arg\alpha-v\) are complex conjugates. The mean of its imaginary part over a full turn is zero. Since the physical curvature is real throughout that turn, \(\operatorname{Im}d=0\). In particular \(c=f(0)=d-\sum_\alpha r_\alpha\) is real.

Suppose \(f\) is nonconstant. If \(c=0\), its first nonzero term is \(v z^n\), \(n>0\). With \(\lambda=i\omega n\), the order-\(n\) coefficient forces \(b=0\). At order \(2n\), the contributions \(2v(\lambda^4 v)\) and \(-2(\lambda v)(\lambda^3v)\) cancel. The remaining coefficient is \(-2av^2\), contradicting \(a>0\).

If \(c\ne0\), the constant coefficient gives \(c^4=2a\). Write \(f=c+v z^n+O(z^{n+1})\), \(v\ne0\), \(n\ge1\). Dividing the first variation at order \(n\) by \(2cv\) yields
\[
 \lambda^4+\tfrac52c^2\lambda^2-(b/c)\lambda+2c^4=0.
\]
Its real part equals
\[
 \bigl((\omega n)^2-5c^2/4\bigr)^2+7c^4/16>0.
\]
Consequently \(f\) is constant. Closure and positive bending exclude zero curvature. Integration of the Frenet equations gives the stated parametrization.

The formal statement is `ClosedSimilarity.ClosedUnitFrenetCurve.rational_exponential_curvature_circle` in [RationalCurvatureCircle.lean](../../SolitonClassification/RationalCurvatureCircle.lean). The hypothesis singles out curvature rational in one arclength frequency. The classification of arbitrary smooth closed similarity profiles remains open.
