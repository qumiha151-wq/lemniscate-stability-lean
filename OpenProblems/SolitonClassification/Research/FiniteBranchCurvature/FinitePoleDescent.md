# Deck invariance of a finite Laurent pole of a similarity curvature

Let \(q\ge1\) be an integer, \(s=s_0+w^q\), and \(f\) a meromorphic germ at \(w=0\) with a pole. Near every sufficiently small nonzero \(w\), suppose \(f\) agrees with an ordinary analytic curvature germ \(k(s)\) in this coordinate, satisfying
\[
 2(kk^{(4)}-k'k''')+3k^2(k')^2+5k^3k''+k^6-2ak^2-2bk'=0 .
\]
The germs \(k\) may vary with \(w\). For every \(\zeta^q=1\), the punctured germ \(f(\zeta w)\) equals \(f(w)\). This local result allows arbitrary complex \(a,b\).

The derivative in the base coordinate is \(D=(q w^{q-1})^{-1}\partial_w\). An order-\(n\) jet with coefficient \(c\) becomes an order-\((n-q)\) jet with coefficient \((n/q)c\); this remains valid as a jet of coefficient zero when \(n=0\). The ordinary chain rule on the local charts gives the pulled-back scalar residual through the fourth derivative. The same operator commutes with deck rotations.

Write \(f\sim c w^n\), \(n<0\), \(t=n/q\). If \(n<-q\), only \(f^6\) contributes at order \(6n\). If \(-q<n<0\), the quadratic derivative part leads at order \(2n-4q\), with coefficient \(-6c^2t(t-1)(t-2)\ne0\). Thus \(n=-q\); the leading equation is \(c^2(c^2+4)(c^2+9)=0\).

Take two solutions with this same leading coefficient. If their difference has a nonzero first coefficient \(d\) at order \(m\) on the cover, set \(u=m/q\). The product difference identity and four differentiations give the following coefficients at order \(m-5q\).

| Principal coefficient | Coefficient of the difference residual |
|---|---|
| \(c^2=-4\) | \(2cd(u+2)u(u-3)(u-4)\) |
| \(c^2=-9\) | \(cd(u+2)(u-5)(2u^2-4u-21)\) |

The quadratic in the second row has no rational root, since \((2u-2)^2=46\) would be a rational square of a nonsquare integer. Consequently \(q\mid m\) in either case.

Now take the second solution to be \(f(\zeta w)\), which has the same leading coefficient because \(\zeta^{-q}=1\). If \(f(w)-f(\zeta w)\) had nonzero first coefficient \(d\) at \(m\), then \(\zeta^m=1\). The sum of the first \(j\) rotated copies of this difference is \(f(w)-f(\zeta^j w)\) and has coefficient \(jd\) at the same order. For \(j=q\) it is identically zero, contradicting \(qd\ne0\). This proves invariance without any choice of a primitive root.

The local statement assumes meromorphicity at the covering puncture. Bounding an initially unrestricted branch there, and assembling single-valued continuation on the entire base plane, are separate parts of the global argument.

## Recovery of the regular support variables

Suppose instead that \(f\) stays bounded on the covering punctured disk. The same ordinary scalar curvature charts determine \(v=Df\), \(F=Dv+f^3/2\) and \(h=(DF+b)/f\) wherever \(f\ne0\). With \(J=q w^{q-1}\), their derivatives in \(w\) obey
\[
   f_w=Jv,\qquad v_w=J(F-f^3/2),\qquad F_w=J(fh-b),\qquad h_w=J(a-fF).
\]
For the last identity on an ordinary chart, differentiate \(h=(F'+b)/k\). The numerator in \(h'-(a-kF)\), after multiplication by \(k^2\), is precisely half the ordinary scalar residual. Pullback gives the claimed derivative in \(w\). A bounded curvature branch has a holomorphic filling. If that filling is identically zero the deck conclusion is immediate. Otherwise isolated zeros give \(f\ne0\) throughout a sufficiently small punctured neighborhood, where the reconstructed fields supply the hypotheses of the bounded support theorem.

Together the two cases imply that a meromorphic covering germ built from the ordinary scalar curvature charts is invariant under every deck rotation, without separately prescribing velocity, force, support, a leading coefficient, or pole order.
