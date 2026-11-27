# Closed similarity profiles with elliptic arclength curvature

For a smooth immersed closed plane curve satisfying the free-elastic similarity law, suppose its signed arclength curvature extends meromorphically to the complex plane, agrees with the curvature on the real axis, and has a period with nonzero imaginary part. The extension is holomorphic along the real axis. Then the curve parametrizes a covered circle or a covered Bernoulli lemniscate. In the latter case the angular coefficient of its similarity generator vanishes.

The proof allows any bending energy, arbitrary translation and rotation coefficients, and multiple covers. The nonreal period can be a period of meromorphic germs, so the values assigned at individual poles do not matter. The positive real period is supplied by the closed immersion itself. The theorem applies in particular to elliptic functions of arbitrary degree and period lattice.

## From the curve to a complex identity

Let \(k\) denote signed curvature, \(a\) the dilation coefficient, and \(b\) the rotation coefficient. Centering the similarity when its linear part is nonzero yields a periodic support profile with \(a>0\). The remaining case would be a closed translator, excluded by the position equation. The force \(F=k''+k^3/2\) obeys
\[
 k F''-k'(F'+b)=k^2(a-k F).
\]
Differentiation of the complex extension along the real axis reproduces the actual arclength derivatives. The meromorphic identity theorem gives the following equality of punctured germs at every complex point:
\[
 2(kk''''-k'k''')+3 k^2(k')^2+5k^3 k''+k^6-2ak^2-2bk'=0.
\]
The same identity theorem transfers the real period to the normalized complex continuation.

## Local poles and global rigidity

At a pole \(s_0\), put \(u=s-s_0\). The fourth-order identity implies
\[
 k(s_0+u)=\frac{c}{u}+u^3 R(u),\qquad c\in\{3i,-3i\},
\]
with \(R\) holomorphic at zero. In particular the function \(D=k''+2k^3/9\) has a removable singularity there and takes the value zero. The proof derives the pole order and each required Laurent coefficient from the equation. [Local calculation](OrdinaryPoleExpansion.md)

The regularized \(D\) is entire and has both periods. Each complex number can be brought into a bounded rectangle by subtracting integer multiples of those periods. Liouville's theorem makes \(D\) constant. If \(k\) has a pole, the constant is zero. If it has none, the same argument makes \(k\) itself constant.

## Position and covering multiplicity

A constant curvature on a closed unit-speed immersion has a nonzero value \(K\) and yields \(X(s)=O+Z e^{iKs}\), with \(Z\ne0\). In the other case, on the real axis \(k''+2k^3/9=0\). Using the first integral, an upward crossing of zero curvature, uniqueness of the oscillator, and the Frenet equations gives the full parametrization
\[
 X(s_0+d A(u))=X(s_0)+dR\frac{\sin u}{1+i\cos u},\qquad |R|=1,
 \quad A(u)=\int_0^u (1+\cos^2 v)^{-1/2}\,dv .
\]
Here \(d>0\), \(a d^4=15/2\), and \(b=0\). The given curve period equals \(m d A(2\pi)\) for some positive integer \(m\). Hence the statement identifies both lobes and the multiplicity of the actual curve in position.

[Physical classification theorem](../../SolitonClassification/EllipticArclengthClassification.lean) · [Bernoulli position and cover theorem](../../SolitonClassification/BernoulliPhysicalCover.lean) · [Verified rotating example outside this class](../../SolitonClassification/EllipticRotatingObstruction.lean)

