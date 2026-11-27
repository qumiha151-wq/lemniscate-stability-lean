# A common physical disk up to initial bending defect \(11/2\)

Let \(X\) be a smooth closed immersed planar free elastic flow, \(L\) its length, \(B=\int k^2ds\), \(c=L^{-1}\int X ds\), and \(R=2\pi/B\). Suppose initially \(LB-4\pi^2\le11/2\). For every \(0\le s\le t\) during its smooth lifetime,
\[
 \overline B\bigl(c(s),\,0.846R(s)+0.004R(t)\bigr)
       \ \subseteq\ \operatorname{conv} X(t).
 \tag{1}
\]
In particular a physical disk of radius \(0.850R(s)\) about \(c(s)\) lies in every subsequent hull. Finite decimals in this proof denote exact rational numbers.

Use the signed physical sublevel theorem at defect 36: \(d=LB-4\pi^2\) is nonincreasing, and turning has absolute value one. Reverse the orientation if necessary. Thus \(0\le d(t)\le11/2\). [Length and turning in the bending sublevel](../../../LengthGrowth/Research/BendingSublevel/DefectThirtySix.md)

## Direct Fourier estimates for the actual tangent

At any time put \(\kappa=2\pi/L,\ \theta=\kappa s,\ \Gamma(\theta)=\kappa(X-c),\ T=\Gamma_\theta,\ K=k/\kappa,\ N=iT\), viewing the plane as \(\mathbb C\). All means and \(L^2\) norms below use \(d\theta/(2\pi)\). Set \(D=d/(4\pi^2)\), \(x=\sqrt D\). Then \(\langle K\rangle=1,\ \langle K^2\rangle=1+D\), and \(x<0.374,\ D<0.14\). Smooth periodicity justifies all Fourier products and differentiated series. If \(t_n=\widehat T(n)\) and \(p_n=|t_n|^2\), closedness gives \(t_0=0\). The unit speed, \(T_\theta=iKT\), and Parseval give
\[
 \sum_n p_n=1,\qquad \sum_n n p_n=1,\qquad
 \sum_n(n-1)^2p_n=D.                                              \tag{2}
\]
The middle identity follows by integrating \(-i\overline T T_\theta=K\).

Write \(W=1-p_1\). Since \(n(n-1)\ge2\) for integers \(n\ne0,1\), (2) implies \(W\le D/2\). The first Fourier coefficient of \(|T|^2=1\) vanishes. Its only term containing \(t_1\) and another nonzero coefficient is \(t_2\overline{t_1}\). Cauchy–Schwarz on all the remaining pairs gives
\[
 |t_2|\sqrt{1-W}\le W,\qquad W\le D/4+3|t_2|^2/4.                \tag{3}
\]
The second assertion uses \((n-1)^2\ge4\) off \(0,1,2\). Inserting \(W\le D/2\) in (3) first gives \(|t_2|^2\le0.038D\) and \(W\le0.279D\). Reinserting the latter gives \(|t_2|^2\le0.012D\), \(W\le0.259D\le0.26D\), and finally \(|t_2|\le0.266D\). The case \(D=0\) obeys all the bounds directly.

The nonzero position modes are \(t_n/(in)\). The constant mode of \(\Gamma\) is zero. Its first mode is a circle of radius \(\sqrt{1-W}\). Its remaining harmonics after \(n=1,2\) have total amplitude at most
\[
 x\left(\sum_{n\notin\{0,1,2\}}\frac{1}{n^2(n-1)^2}\right)^{1/2}
 = x\sqrt{2\pi^2/3-25/4}<0.575x.                                 \tag{4}
\]
For the sum use \(1/[n^2(n-1)^2]=1/n^2+1/(n-1)^2-2/[n(n-1)]\), telescope the last sum on the two tails, and use \(\sum_{j\ge1}1/j^2=\pi^2/6\). Including \(n=2\) gives error at most \(h=0.575x+0.133D\). In every direction the support of \(\Gamma\) is at least \(\sqrt{1-W}-h\), and \(\|\Gamma\|_\infty\le1+h\).

For \(n\in\mathbb Z\setminus\{0,2\}\),
\[
 (1-1/n)^2\le(5/9)(n-1)^2-(8/9)(n-1).
\]
Indeed the difference multiplied by \(9n^2\) equals \((n-1)(n+1)(n-3)(5n-3)\), nonnegative at all the indicated integers. At \(n=2\) the correction needed is \(7/12\). Thus the Fourier coefficients of \(\Gamma+iT\), together with (2), give
\[
 \|\Gamma+iT\|_2^2=\sum_{n\ne0}(1-1/n)^2p_n
     \le 5D/9+7|t_2|^2/12\le(0.75)^2D .
\]
It follows for the actual normal and curvature that
\[
 \|k(X-c)+N\|_2=\|(K-1)\Gamma+\Gamma+iT\|_2
 \le x(1+h+0.75).
 \tag{5}
\]

## The physical flow

Use \(F=k_{ss}+k^3/2,\ E=B/2,\ Y=\int F^2ds\). For \(X_t=-FN\) in normal gauge the force balance, dilation virial, energy dissipation and centroid variation give
\[
 \int FN ds=0,\quad E=-\int F(X-c)\cdot N\,ds,\quad E'=-Y,\quad
 Lc'=\int F[k(X-c)+N]\,ds .
\]
The centroid and virial identities follow from \([(k^2/2)T+k_s N]_s=FN\) and \((ds)_t=kFds\). Centered Wirtinger or direct Fourier comparison yields \(\int|X-c|^2ds\le L/\kappa^2\). Hence \(E\le\sqrt{YL}/\kappa\) and \(R'=\pi Y/E^2>0\). As \(EL=\tfrac12(2\pi)^2(1+D)\), (5) proves the physical comparison
\[
 |c'|\le (1+D)x(1.75+h)R' .
\]
For support use \(1/\kappa=(1+D)R\) and \(\sqrt{1-W}\ge1-0.132D\). The latter follows by squaring, since \(W\le0.26D,\ D\le0.14\). Uniformly on \(0\le x\le0.374\),
\[
 (1+x^2)x(1.75+0.575x+0.133x^2)<0.846,\quad
 (1+x^2)(1-0.575x-0.265x^2)>0.852.
 \tag{6}
\]
The first polynomial is increasing. For the second, its derivative is \(-0.575+1.47x-1.725x^2-1.06x^3<0\) since \(1.47(0.374)<0.575\). At \(x=0.374\) the two values are \(0.8456585157\ldots\) and \(0.8524937229\ldots\). Thus \(|c(t)-c(s)|\le0.846(R(t)-R(s))\) while every directional support exceeds \(0.852R(t)\) beyond \(c(t)\). The earlier-centre bound follows by subtraction and the half-space representation for the compact convex hull. All arguments use the normal velocity of the genuine flow and apply modulo tangential reparametrization.
