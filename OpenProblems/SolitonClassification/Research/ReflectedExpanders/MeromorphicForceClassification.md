# Classification for a single-valued meromorphic force as a function of curvature

**Theorem.** Let a smooth closed immersed plane curve be a similarity profile for free elastic flow. Write its signed curvature as \(k\) and its elastic force as \(F=k_{ss}+k^3/2\). Suppose there is a meromorphic function \(G\) on the whole complex plane such that \(F=G(k)\) on one nonempty open arc on which \(G(k)\) is finite. Then the curve is a covered circle or a covered Bernoulli lemniscate, up to similarity. Both occur. The result holds for meromorphic functions of arbitrary growth.

The global domain matters. At every point where \(k_s\ne0\), analytic inversion already expresses \(F\) locally as a holomorphic function of \(k\).

**Continuation and normalization.** The support ODE makes the profile real analytic. A constant-curvature arc gives constant curvature everywhere and a covered circle. Otherwise extend the equality along the real parameter line. At any finite endpoint of a component on which \(k\) avoids the poles of \(G\), the composition must diverge along points approaching that endpoint, while the actual force is continuous. This excludes such an endpoint. The nonconstant curvature has both signs. At every zero, \(G'(0)k_s=-\omega\), where \(\omega\) is the angular coefficient. Either a zero has \(k_s=0\), or there are both an upward and a downward simple crossing. Hence \(\omega=0\). Normalize the positive dilation coefficient to one. The normal support \(p\) now equals \(P(k)\) for a globally meromorphic \(P\). Rescaling replaces \(G(x)\) by \(\lambda^{-3}G(\lambda x)\), preserving its domain. [Support identities and one-sign rigidity](RationalForceClassification.md)

**An entire differential equation.** Put \(r=P'/x\). On an interval where \(kk_s\ne0\), introduce \(H(k)=k_s^2\). The support equations give

\[
 H'=-x^3-2P,\qquad r'H+\tfrac12 rH'+1+xP=0 .
\]

If \(r'\) vanishes identically, \(P\) is a polynomial of degree at most two, a case excluded for nonconstant curvature by the coefficient comparison below. Otherwise use the second equation to define the meromorphic continuation of \(H\) as \((-1-xP-rH'/2)/r'\), with \(H'\) on the right replaced by \(-x^3-2P\). On a smaller open interval with \(r'\ne0\) this is the original \(H\). Both differential identities therefore hold meromorphically on the plane. Substituting \(P=-(H'+x^3)/2\) and multiplying the second identity by \(-4x^2\) gives

\[
 2xHH'''-2HH''+xH'H''+6x^2H+5x^3H'+2x^6-4x^2=0 .
\]

At a pole \(\zeta\ne0\) of order \(m\), write \(H\sim C(x-\zeta)^{-m}\). The coefficient at order \(2m+3\) is \(-\zeta m(m+1)(3m+4)C^2\). For a pole at zero the coefficient at order \(2m+2\) is \(-3m(m+1)(m+2)C^2\). Neither can vanish, so \(H\) is entire.

**Behavior at infinity.** Suppose \(H\) is transcendental entire. Take maximum-modulus points \(z\) of modulus \(R\) tending to infinity outside the Wiman–Valiron exceptional set. The central index \(N=N(R)\) tends to infinity, \(M(R)=|H(z)|\) grows faster than every fixed power of \(R\), and for \(j=1,2,3\) one has \(H^{(j)}(z)=(1+o(1))(N/z)^jH(z)\) along the same sequence. [Hayman, Theorem 12 and §6.3](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/local-growth-of-power-series-a-survey-of-the-wimanvaliron-method/1AD6F21458C1864036EEDFA3B53FF5D5) · [Wiman–Valiron estimates, Theorem 2.1](https://link.springer.com/article/10.1007/s00208-022-02358-z)

Divide the differential equation at \(z\) by \(N^3H(z)^2/z^2\). The terms \(2zHH'''\) and \(zH'H''\) tend to \(2\) and \(1\). The term \(-2HH''\) tends to zero. The remaining terms have absolute value bounded by a constant times

\[
 \frac{R^4}{N^3 M(R)}+\frac{R^4}{N^2 M(R)}
     +\frac{R^8+R^4}{N^3 M(R)^2},
\]

which tends to zero. The limiting identity \(3=0\) is impossible. Thus \(H\) is a polynomial and so is \(P=-(H'+x^3)/2\). Its coefficients are real because it is real on an interval.

Coefficient comparison gives \(P=-5x^3/18\). An upward inflection has normalized support state \((k,k_s,p,q)=(0,\sqrt{6/5},0,0)\). Uniqueness for the support ODE identifies Bernoulli's lemniscate through that state. Consequently none of the twelve other reflected examples admits this global meromorphic extension on any open arc. The complex-analytic step uses the cited Wiman–Valiron theorem. [Coefficient comparison and identification](RationalForceClassification.md) · [The twelve reflected expanders](ReflectedExpanders.md)
