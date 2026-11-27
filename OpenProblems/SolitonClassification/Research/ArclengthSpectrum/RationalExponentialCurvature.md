# A direct proof for rational functions of one arclength frequency

Let a smooth closed immersed plane curve be a free-elastic similarity profile. If its signed arclength curvature has the form \(k(s)=R(e^{i\omega s})\), with \(R\in\mathbb C(z)\), \(\omega\in\mathbb R\setminus\{0\}\), and no pole on the unit circle, the curve is a circle, possibly multiply traversed. The angular velocity of the similarity is unrestricted. This elementary argument complements the [meromorphic arclength classification](../ReflectedExpanders/MeromorphicArclengthClassification.md).

Write \(a>0\) for the dilation coefficient and \(b\in\mathbb R\) for the angular coefficient, using the fixed similarity center as origin. Positivity of \(a\) for a closed profile follows from the dilation identity. Put \(G=aX+bJX\), \(q=G\cdot T\) and \(F=k''+k^3/2\), with normal \(N=JT\). The soliton law is \(F=-G\cdot N\). Differentiating in arclength gives
\[
 q'=a-kF,\qquad kq=b+F'.
\]
The identically zero curvature cannot close a regular curve. In \(z=e^{i\omega s}\) set \(D=i\omega z\,d/dz\), \(K=R\) and \(F=D^2K+K^3/2\). The rational function \(H=(b+DF)/K\) agrees with \(q\) wherever the original curvature is nonzero. Consequently \(DH=a-KF\) and \(KH=b+DF\) hold as rational identities.

At \(z=0\), \(D\) preserves an existing pole order. If \(K\) had a pole of order \(n>0\), the orders of the poles of \(F\) and \(DH\) would be \(3n\) and \(4n\). Then \(H\) would have order \(4n\) and \(KH\) order \(5n\), contradicting \(KH=b+DF\). Thus \(K\), \(F\) and \(H\) are regular at zero, the last assertion following from \(DH=a-KF\). With \(c=K(0)\), the constant terms give \(c^4=2a\) and \(H(0)=b/c\).

At a finite pole \(\alpha\ne0\) use the local coordinate \(u=(i\omega)^{-1}\log(z/\alpha)\), so \(D=d/du\). If \(K\) had pole order \(n>1\), its cubic would dominate \(K''\). Then \(H'\) would have order \(4n\), \(H\) order \(4n-1\), and the two sides of \(KH=b+F'\) would have different orders \(5n-1\) and \(3n+1\). Every such pole is simple. Write \(K=r/u+O(1)\) and \(f=2r+r^3/2\). If \(f=0\), then \(r^2=-4\). Otherwise \(F\sim f/u^3\), \(H\sim rf/(3u^3)\) by the derivative identity, and \(r^2f/3=-3f\) by the product identity. This gives \(r^2=-9\). In either case the residue \(\beta_\alpha\) of \(K\) in the \(z\)-coordinate obeys \(\beta_\alpha/\alpha=i\omega r\in\mathbb R\).

Reality of \(k\) on the unit circle gives the rational identity \(K(z)=\overline{K(1/\bar z)}\). Thus \(K(\infty)=\bar c\), so ordinary partial fractions give
\[
       c-\bar c=-\sum_{\alpha\ne0}\beta_\alpha/\alpha .
\]
The right side is real. Hence \(c\) is real and nonzero.

If \(K\) is nonconstant, let \(A z^n\), \(n\ge1\), be its first nonconstant Taylor term at zero. The identity for \(KH\) gives \(H=b/c+Bz^n+O(z^{n+1})\) for some \(B\). Put \(\lambda=i\omega n\). Matching order \(n\) in both identities gives
\[
 \lambda B=-(c\lambda^2+2c^3)A,\qquad
 cB+(b/c)A=\lambda(\lambda^2+3c^2/2)A .
\]
As \(A\ne0\), elimination forces \(\lambda^4+(5/2)c^2\lambda^2-(b/c)\lambda+2c^4=0\). Its real part is \(\big((\omega n)^2-5c^2/4\big)^2+7c^4/16>0\). Consequently \(K\) is constant. Integrating the unit-speed Frenet equations for its nonzero curvature gives a parametrized circle.

**Verification scope.** The finite Fourier subclass and the resulting classification for periodic curvature satisfying a polynomial-coefficient linear differential equation are kernel-checked in the adjacent Lean project. The rational-function argument above is a written proof. Its complex pole expansions and partial-fraction step have not been formalized here.
