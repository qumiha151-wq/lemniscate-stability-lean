# Classification from one observed coordinate in arclength

Let \(X(s)\) be a smooth closed regular plane similarity profile for the free elastic flow. Use unit speed and any full period \(L\). Consider one real-valued observation
\[
              h(s)=A|X(s)|^2+b\cdot X(s)+c,\qquad (A,b)\ne(0,0).
\]
For \(A=0\) this measures height in a prescribed direction. For \(A\ne0\), completing the square makes it a rescaled squared distance from an arbitrary point, plus a constant.

1. If on any open arc \(h\) is algebraic over the field of single-valued meromorphic functions of complex arclength on \(\mathbb C\), the profile is a circle or Bernoulli's lemniscate, up to similarity and covers. All these observations of both profiles satisfy this condition.
2. If on any open arc \(h\) extends to an entire function of complex arclength, the profile is a circle. The same conclusion follows if the germ satisfies a nontrivial homogeneous linear differential equation with polynomial coefficients in \(s\). Circles satisfy both hypotheses for every choice of \(A,b,c\).
3. For each individual noncircular profile there exists \(\eta>0\) such that every such observation, for every direction and centre, has
\[
          \limsup_{n\to\infty}|\widehat h(n)|^{1/n}\ \ge\ \eta,
\quad
          \widehat h(n)=L^{-1}\int_0^L h(s)e^{-2\pi i n s/L}\,ds .
\]
All the observations are real analytic and have exponentially decaying Fourier coefficients. The lower bound is on the exponential rate along a subsequence. It can depend on the particular profile and the chosen period.

## Recovery of curvature

For a unit vector \(e\), the height \(u=e\cdot X\) satisfies \(u'=e\cdot T\) and \(u''=k e\cdot N\). Consequently
\[
                         (1-u'^2)k^2=u''^2 .
\]
The first factor cannot vanish identically on an interval. Analyticity would extend the identity to every real \(s\), forcing a constant unit tangent and preventing closure. For \(u=|X-z|^2\), write \(q=(X-z)\cdot T\), \(p=(X-z)\cdot N\). Then \(u'=2q\), \(q'=1+kp\) and \(p^2=u-q^2\), giving
\[
                         (u-u'^2/4)k^2=(u''/2-1)^2 .
\]
If \(p\) vanished identically, \(q'=1\) would contradict periodicity. The two displayed identities are kernel-checked in Cartesian arclength coordinates for every choice of \(e\) or \(z\). [ScalarObservation.lean](../../SolitonClassification/ScalarObservation.lean)

Algebraic germs over a meromorphic differential field form a differential field in characteristic zero. Indeed differentiating an irreducible polynomial for a germ gives its derivative by dividing by the nonzero formal derivative of that polynomial in its last variable. Thus the relevant quotient on a smaller open arc shows that \(k\) is algebraic over the same meromorphic field. The classification of algebraic extensions of meromorphic arclength curvature gives the asserted two possibilities. [Meromorphic arclength classification and its algebraic extension](../ReflectedExpanders/MeromorphicArclengthClassification.md)

## The observations of the Bernoulli curve

Normalize the dilation coefficient to one and put the expansion centre at zero. Write \(v=k'\) and \(b_0=\sqrt{6/5}\). The curvature is a nonconstant elliptic function and satisfies \(v'=-2k^3/9,\ v^2+k^4/9=b_0^2\). The supports are \(p=-5k^3/18,\ q=5kv/6\). The elliptic function \(w=(v+i k^2/3)/b_0\) has modulus one on the real line and obeys \(w'=(2i/3)kw\). Therefore the complex unit tangent \(T=T_x+iT_y\) satisfies \(T^2=C w^3\) for a nonzero constant \(C\), since \(T'=ikT\). Its reciprocal on the real line recovers \(T_x-iT_y\). Both tangent components are algebraic over the field of elliptic functions for the period lattice of \(k\). The support reconstruction \(X=qT+pN\) gives the same property for both position components and all the observations in the theorem. Rigid motions and changes of scale preserve the assertion with the correspondingly transformed lattice. [Bernoulli curvature and its elliptic continuation](../ReflectedExpanders/MeromorphicArclengthClassification.md) · [Support formulas](../ReflectedExpanders/RationalForceClassification.md)

An entire function algebraic over an elliptic function field is constant. Each translation by an element of the period lattice solves the same fixed polynomial equation. The field of meromorphic functions on the plane contains at most its degree many distinct roots. Each of two independent periods therefore has a nonzero integer multiple that is an actual period of the entire function. Boundedness on their compact period parallelogram and Liouville's theorem give constancy. On a closed regular immersion a constant height would place the image in a line. A constant squared distance would place it on a circle of positive radius and make it a cover of that circle. This excludes every entire observation for Bernoulli. Circle coordinates and squared distances from fixed points are constants plus sine and cosine in arclength, so they are entire.

If \(\sum_j p_j(s)h^{(j)}(s)=0\) on an open arc, analyticity extends this to the real line. Let \(d\) be the largest degree of a nonzero \(p_j\). Replacing \(s\) by \(s+nL\) leaves all the derivatives unchanged and makes the left side a polynomial in \(n\) vanishing for every integer \(n\). Its coefficient of \(n^d\) is the nontrivial constant-coefficient equation with coefficients \(L^d[s^d]p_j\). All solutions of this equation extend to entire functions by the linear constant-coefficient initial value problem.

## Uniformity over directions and centres

Let \(V\) be the real span of \(1,X_x,X_y,|X|^2\), modulo constants. It has finite dimension. For every positive integer \(j\), the vectors whose real-periodic representatives extend holomorphically to \(|\operatorname{Im}s|<j\) form a linear subspace \(V_j\). The subspaces decrease and their intersection is zero for a noncircular profile by part 2: nested continuations agree on overlaps. Finite dimensionality implies \(V_J=0\) for some finite \(J\). Every observation specified in the theorem is nonconstant on this profile. If its positive-index Fourier coefficients had root limsup strictly less than \(e^{-2\pi J/L}\), the negative-index coefficients would have the same decay by reality. Its Fourier series would extend holomorphically across this strip, with uniform convergence on compact substrips, and agree with the observation on the real line. This contradiction proves part 3. The upper exponential bound follows by continuation from real analyticity around a compact real period and by shifting the Fourier integration contour inside that strip.

The finite-dimensional classification and the Fourier conclusion above are analytic arguments. Lean verifies the two geometric recovery identities without an analytic continuation hypothesis.
