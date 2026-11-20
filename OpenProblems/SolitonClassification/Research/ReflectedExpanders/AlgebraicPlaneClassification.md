# Algebraic plane images of closed free-elastic similarity profiles

**Theorem.** Let \(X(s),Y(s)\) be a smooth closed free-elastic similarity profile parametrized by arclength. If one nonempty open arc is contained in the zero set of a nonzero polynomial in the two position coordinates, the profile is a circle or Bernoulli's lemniscate, up to similarity, reparametrization and multiple covers. Both shapes have algebraic plane images. The same classification holds under the distinct hypothesis that a nonzero polynomial in signed curvature and elastic force vanishes on some open arc.

The proof uses ordinary local expansions for the curvature in complex arclength. It does not assume that arclength is an algebraic parameter of a plane curve.

## From a one-dimensional state field to meromorphic arclength curvature

Let \(D=d/ds\). For real dilation coefficient \(a>0\), angular coefficient \(\omega\), curvature \(k\), its derivative \(v\), elastic force \(F\), and auxiliary support \(h\), the equations are
\[
 Dk=v,\qquad Dv=F-k^3/2,\qquad DF=kh-\omega,\qquad Dh=a-kF.
\]
View these as germs of analytic functions at a regular real parameter value. Suppose \(k\) is nonconstant and the finitely generated function field \(K=\mathbb C(k,v,F,h)\) has transcendence degree one. We claim that \(k\) extends as a single-valued meromorphic function to the whole complex arclength plane.

Indeed \(K\) is the meromorphic function field of its smooth connected projective curve \(S\). The equations make \(D\) a nonzero derivation of \(K\), hence a meromorphic vector field on \(S\). Locally in a uniformizer \(u\in K\) it is \((Du)\partial_u\). Such a uniformizer can be taken in \(K\) at every point, since the local ring of the smooth algebraic curve is a discrete valuation ring.

Suppose \(D\) has a pole of order \(m\ge1\). Then \(ds/du=1/(Du)\) has a zero of order \(m\); its local primitive satisfies \(s-s_* =c u^{m+1}(1+O(u))\) with \(c\ne0\). The meromorphic functions \(k,v,F,h\) on \(S\) give convergent Laurent–Puiseux series in \(s-s_*\) with finite principal parts and satisfy the displayed equations. The local expansion calculation in the arclength classification proves that \(k\) has an ordinary Taylor or Laurent series in \(s-s_*\). That calculation applies to every such local solution, at any finite \(s_*\), including at a zero of \(k\). Then \(v=Dk,\ F=D^2k+k^3/2,\ h=(DF+\omega)/k\) also are ordinary meromorphic germs in \(s-s_*\). The quotient is valid as an identity of germs because \(k\) is nonconstant. Every nonzero element of \(K\) is therefore meromorphic in \(s-s_*\) and its order in \(u\) is a multiple of \(m+1\). This contradicts the existence of the element \(u\in K\) of order one. [Local arclength expansion and classification](MeromorphicArclengthClassification.md)

It follows that \(D\) is holomorphic on the compact curve \(S\). Its flow exists for every complex time. For instance a finite cover by coordinate neighborhoods with smaller relatively compact interiors gives a uniform positive time radius for holomorphic local solutions. Composing the local time maps along subdivisions of any time segment extends them, and uniqueness plus the group law makes these continuations single-valued on the simply connected time plane. A generic real point of the given germ determines a nonsingular state point of \(S\), and the flow there agrees with the original state by uniqueness. Pulling back the meromorphic function \(k\) along this nonconstant entire orbit produces the claimed meromorphic continuation. The arclength classification now identifies the given profile. [Meromorphic arclength classification](MeromorphicArclengthClassification.md)

## Algebraic plane images

Let a nonzero polynomial vanish on a real open arc of the image. Its irreducible complex factors are finite in number, so some irreducible factor vanishes identically on a subarc. By analyticity it vanishes throughout. Select a regular point of that plane algebraic curve along the arc and an orthonormal coordinate choice with \(DX\ne0\). Such points exist because the singular points of an irreducible plane algebraic curve are isolated and the immersion is regular.

The plane function field \(\mathbb C(X,Y)\) is a finite extension of \(\mathbb C(X)\). Differentiation \(d/dX\) preserves it since characteristic is zero. In particular \(Y_X\) belongs to it. Unit speed gives \((DX)^2(1+Y_X^2)=1\), so adjoining \(DX\) gives another finite extension \(K_1\) still of transcendence degree one. The derivation \(d/dX\) extends to \(K_1\), and \(D=(DX)d/dX\) preserves \(K_1\). Thus \(k=(DX)(D^2Y)-(DY)(D^2X)\), \(v\), \(F\), and \(h=(DF+\omega)/k\) all lie in \(K_1\) if \(k\) is nonconstant. Their subfield \(K\) has transcendence degree one, and the preceding argument applies. A constant curvature gives a circle. The circle is quadratic; Bernoulli's lemniscate in suitable Cartesian coordinates has equation \((X^2+Y^2)^2=c(X^2-Y^2)\), \(c>0\).

## Algebraic relations between curvature and force

Assume a nonzero polynomial vanishes at \((k,F)\) on an open arc of a nonconstant profile. Choose a smaller arc where \(kv\ne0\). The germ \(P=F\) is algebraic over \(\mathbb C(k)\). Write primes in this paragraph for differentiation relative to \(k\), and put \(r=P'/k\); both \(P'\) and \(r'\) belong to \(\mathbb C(k,P)\). From \(h=rv+\omega/k\) and the real support equations one obtains
\[
 r'v^2-\frac{\omega}{k^2}v+
 r(P-k^3/2)-a+kP=0 .
\]
If the polynomial in \(v\) on the left is nonzero over \(\mathbb C(k,P)\), it makes \(v\) algebraic over this field. The formula for \(h\) then makes \(K\) a field of transcendence degree one, proving the result. Otherwise its leading and linear coefficients give \(r'=0,\ \omega=0\). On the real arc \(r\) is constant and \(P=c_2 k^2+c_0\). The rational-force classification applies directly. The converse holds because circle force is constant and Bernoulli force is \(5k^3/18\). [Rational-force classification](RationalForceClassification.md)
