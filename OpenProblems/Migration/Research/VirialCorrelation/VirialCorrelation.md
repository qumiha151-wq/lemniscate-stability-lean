# A common physical disk at initial bending product \(5\pi^2\)

Let \(X\) be a smooth closed immersed planar free elastic flow, \(E=\frac12\int k^2\,ds\), \(L=\int ds\), \(c=L^{-1}\int X\,ds\), and \(R=\pi/E\). If \(2E(s)L(s)\le5\pi^2\), then at each later smooth time \(t\),
\[
 \overline B\!\left(c(s),\,\frac45R(s)+\frac1{500}R(t)\right)
 \ \subseteq\ \operatorname{conv} X(t).
\]
Since \(R\) is nondecreasing, the fixed disk of radius \(401R(s)/500\) centered at \(c(s)\) persists. For a classical forward flow the fixed disk also persists from initial data at time zero when the positive-speed initial immersion and its position, speed and curvature satisfy the one-sided continuity hypotheses in the Lean theorem. Hence separation of two material traces into opposite open half-planes requires \(L(0)\int k(0)^2\,ds>5\pi^2\). The previous initial-data threshold was \(4\pi^2+11/2\). Flows above the new threshold remain outside this result.

## A product estimate from the same physical force

Use the arclength force \(F=k_{ss}+k^3/2\), curvature scale \(\kappa=2\pi/L\), angular arclength \(\theta=\kappa s\), unit tangent \(T\), and \(N=iT\). Set \(\Gamma=\kappa(X-c)\), \(K=k/\kappa\), \(H=K\Gamma+N\), \(p=N\cdot\Gamma\) and \(q=T\cdot\Gamma\). Brackets denote the normalized mean over \(\theta\in[0,2\pi]\). The dilation virial and the projected centroid variation give \(E=-(L/\kappa)\langle Fp\rangle\) and \(c'=\langle FH\rangle\). Energy dissipation gives \(R'=\pi L\langle F^2\rangle/E^2\).

In any real inner product space,
\[
 2|\langle P,F\rangle\langle F,Q\rangle|
 \le \|F\|^2\bigl(\|P\|\|Q\|+|\langle P,Q\rangle|\bigr).
\]
Indeed the vector \(2\langle P,F\rangle F-\|F\|^2P\) has norm \(\|F\|^2\|P\|\). Pair it with \(Q\) and use Cauchy–Schwarz. Apply this to \(P=p\) and \(Q=e\cdot H\) for every unit vector \(e\). Write \(D=2EL/(4\pi^2)-1\). This proves the physical bound
\[
 |c'|\le R'\frac{1+D}{2}
    \left(\|p\|_2\|H\|_2+|\langle pH\rangle|\right).
\]
The same inequality follows for each projected rate without division by the dissipation. Centered Wirtinger gives \(\|p\|_2\le\|\Gamma\|_2\le1\). The previously verified sublevel theorem at defect \(36\) propagates \(0\le D\le1/4\) and gives turning number of absolute value one. Reflect the plane if needed so that \(\langle K\rangle=1\).

## The cubic correlation

The equations \(\Gamma_\theta=T\) and \(T_\theta=iKT\) imply \(q_\theta=1+Kp\) and \(pN=\Gamma-qT\). Consequently
\[
 (q\Gamma)_\theta=pH+2qT
                  =pH+\Gamma+\overline\Gamma T^2.
\]
Integrating and using \(\langle\Gamma\rangle=0\) gives \(\langle pH\rangle=-\langle\overline\Gamma T^2\rangle\).

Let \(t_n=\widehat T(n)\), \(A=t_1\), \(T_1=Ae^{i\theta}\), \(\Gamma_1=-iT_1\), \(v=T-T_1\), \(w=\Gamma-\Gamma_1\) and \(W=1-|A|^2\). Orthogonal projection gives \(\|v\|_2^2=W\) and \(\|w\|_2^2=\|\Gamma\|_2^2-|A|^2\le W\). As \(\overline{\Gamma_1}T_1=i|A|^2\) is constant, both \(T_1\) and \(v\) have zero mean, and \(\widehat\Gamma(2)=-it_2/2\), expansion yields
\[
 \langle\bar\Gamma T^2\rangle
 =\langle\overline{\Gamma_1}v^2\rangle
   +A^2\overline{\widehat\Gamma(2)}
   +\langle\bar w(T^2-T_1^2)\rangle .
\]
The first term has magnitude at most \(W\). For the last, \(|T+T_1|\le2\) gives a bound \(2\|w\|_2\|v\|_2\le2W\). Hence
\[
 |\langle pH\rangle|\le3W+|t_2|/2.
\]

## Explicit constants for actual material slices

Put \(z=|t_2|\) and \(x=\sqrt D\). The Fourier moment identities for the actual closed unit tangent give
\[
 W\le D/2,\qquad W\le D/4+3z^2/4,\qquad z^2(1-W)\le W^2.
\]
For \(D\le1/4\), successive substitutions give \(z^2\le0.072D\), \(W\le0.305D\), \(z^2\le0.026D\), and \(W\le0.27D\). The last correlation inequality now gives \(z\le0.28D\). Thus \(|\langle pH\rangle|\le0.95D\). All decimals below denote exact rationals.

The previously proved inverse Fourier multiplier estimate for the position modes outside \(\{0,1,2\}\) gives a uniform bound \(0.575x\). Adding the second position mode gives \(h=0.575x+0.14D\) for the distance to the first position harmonic. Its amplitude is at least \(1-0.139D\), by squaring the bound on \(W\). The physical support in every direction beyond \(c\) is at least
\[
 R(1+D)(1-0.575x-0.279D).
\]
The tangent multiplier estimate \(\|\Gamma+iT\|_2^2\le5D/9+7z^2/12\) gives \(\|\Gamma+iT\|_2\le0.755x\). Since \(\|\Gamma\|_\infty\le1+h\) and \(\|K-1\|_2=x\), it follows that \(\|H\|_2\le x(1.755+h)\).

For \(0\le x\le1/2\), exact polynomial bounds give
\[
 \frac{1+x^2}{2}\bigl(x(1.755+0.575x+0.14x^2)+0.95x^2\bigr)<0.800,
 \qquad (1+x^2)(1-0.575x-0.279x^2)>0.803.
\]
Integrating the projected drift therefore costs at most \(0.8(R(t)-R(s))\). Subtract it from the later support. The half-space characterization of a compact convex hull gives the stated disk with a strict support margin. The formal proof applies the projected inequalities directly in material coordinates and passes to initial time through one-sided limits.

