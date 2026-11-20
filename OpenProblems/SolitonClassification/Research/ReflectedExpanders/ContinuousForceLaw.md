# A rotating closed profile has different forces at the same curvature

Let \(k\) be signed curvature, \(F=k_{ss}+k^3/2\) the elastic force, \(a\) the dilation coefficient and \(\omega\) the angular coefficient. For a closed profile with nonconstant curvature, if \(F=G(k)\) for a continuous real function \(G\), then \(\omega=0\). This is the statement of \(\mathtt{angular\_rate\_zero\_of\_continuous\_force\_law}\) in the independent SolitonClassification project.

In geometric terms, each noncircular rotating profile has two points with the same signed curvature and different elastic forces. Indeed, if every two equal curvatures gave equal forces, \(F\) would factor through \(k\) as a function on the compact curvature interval. That factor is continuous because the continuous surjection from a compact parameter circle to its curvature interval is a quotient map. Extending the factor constantly beyond the two ends of the interval gives a continuous \(G\) on the line.

For the identity behind the result, set \(h=aq-\omega p\) in the tangent and normal support coordinates. Then \(F'=kh-\omega\). For any continuously differentiable test function \(w\),

\[
 \int_s^{s+L} w(k)(kh-\omega)\,ds'=0.
\]

In fact this integrand is the derivative of \(w(k)F-J(k)\), where \(J'(x)=w'(x)G(x)\). The primitive is periodic. Every noncircular closed profile has a zero of curvature. If \(\omega\ne0\), take a nonnegative \(C^1\) test function positive at zero and supported where \(|k|\sup|h|<|\omega|\). Then \(\omega\,w(k)(\omega-kh)\) is everywhere nonnegative and strictly positive at a zero of curvature. Its integral must be positive, in contradiction with the identity. The proof only differentiates the smooth physical force and the test function. Continuity suffices for \(G\).

The finite proof of the Bernoulli cubic coefficient uses \(\mathtt{cubic\_support\_at\_simple\_inflection}\) in CubicSupportRigidity. The complex analytic and algebraic classifications are developed in the accompanying papers. [Algebraic plane profiles](AlgebraicPlaneClassification.md) · [Meromorphic arclength curvature](MeromorphicArclengthClassification.md) · [Meromorphic force laws](MeromorphicForceClassification.md)
