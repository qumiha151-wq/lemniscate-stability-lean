# Rapid transverse instability of the matched thin expanding solutions

Consider the matched sequence of smooth closed zero-turn free elastic expanders \(X_b\), with coefficient one and central curvature slope \(b\to\infty\). There exist constants \(c,\eta>0\), independent of \(b\), such that for every sufficiently large matched \(b\) the linearization \(G_b\) of the actual similarity-normalized equation has at least \(\eta b\) eigenvalues with
\[
                         \operatorname{Re}\lambda\ge c b^2
\]
in each of the four character spaces of the two coordinate reflections. Multiplicities are algebraic. The reflections are about the tip axis and its perpendicular. In particular there are growing modes preserving the perpendicular-axis symmetry and breaking the tip-axis symmetry, which permits transverse motion. The result gives no sign for the displacement of the complete curve.

At physical time \(t=20\) the reference curve has expanded by three. In a fixed normal graph chart after undoing this reference dilation, the actual solution map at the reference has derivative of norm at least \(3^{cb^2}\), in each character space. The rate concerns the normalized shape of true solutions on a fixed finite interval.

## Normal linearization

Use \(N=JT,\ T_s=kN,\ F=k_{ss}+k^3/2=-X\cdot N\), with \(s\) arclength on the normalized fixed profile. Dividing the real curve by \(\rho(t)=(1+4t)^{1/4}\), and writing \(\tau=\log\rho\), gives normalized normal speed \(-F-X\cdot N\). For a variation \(uN\) about the fixed profile one has \(\delta k=u_{ss}+k^2u,\ [\delta,\partial_s]=ku\partial_s,\ \delta N=-u_sT\). With \(q=X\cdot T\), differentiation gives
\[
 G_bu=-u_{ssss}-\tfrac52(k^2u_s)_s
      -(3k_s^2+4kk_{ss}+\tfrac32 k^4)u-u+qu_s .                \tag{1}
\]
For example, direct periodic integration by parts gives the physical-arclength identity
\[
 \langle k,G_b k\rangle
   =\int \left(\tfrac16k^6-\tfrac73 Fk^3-F^2-\tfrac32 k^2\right)ds . \tag{2}
\]
Indeed \(\int k^2 k_s^2=-\int k^3 k_{ss}/3\), \(k_{ss}=F-k^3/2\), and \(q_s=1-kF\). The first-order term in (1) makes spectral analysis necessary in addition to the quadratic form.

## A positive density of localized test functions

Set \(x=\sqrt b\,s,\ K=k/\sqrt b,\ f=F/b^{3/2}\). The \(x\)-circle has period \(\ell_b\asymp b\). The matched-profile estimates give \(|X|=O(\sqrt b)\), \(|K|+|K_x|\le C\), and \(K_{xx}=-K^3/2+f,\ |f|\le C/b\). In a fixed first-quarter slow-time interval \(\alpha\le x/b\le\beta<\tau_*\), \(0<\alpha<\beta\), the stress amplitude \(\sqrt{K_x^2+K^4/4}\) is bounded below by a positive constant. These suffice for the argument. [Matched profile and quantitative limiting estimates](OptimalExteriorDefect.md)

On the periodic complex \(L^2(dx)\) space write \(b^{-2}G_b=A+B\) in the unitarily rescaled coordinate, with domains \(H^4_{\rm per}\), where
\[
 \begin{split}
 A u&=-u''''-\tfrac52(K^2u')'-(3K'^2+4KK''+\tfrac32K^4)u,\\
 B u&=(q/b^{3/2})u'-u/b^2 .
 \end{split}                                                       \tag{3}
\]
The self-adjoint operator \(A\) is the operator of its regular periodic fourth-order form. Boundedness of the coefficients and the Fourier interpolation inequality yield
\[
             (Au,u)\le -\tfrac12\|u''\|_2^2+C\|u\|_2^2.          \tag{4}
\]
All constants here and below are independent of the increasing period.

On every unit subinterval inside the chosen slow band, \(\int K^6 dx\ge d>0\) for large \(b\). If this failed, translating a violating unit interval to \([0,1]\) and extracting a \(C^1\)-subsequence using the uniform second derivative bound would give a zero function, contradicting the lower stress bound. For a block of length \(H>4\) inside the band, use \(u=\chi K\) where \(\chi=1\) off two unit endpoint intervals and \(\chi\) vanishes smoothly near the ends with two uniformly bounded derivatives. In the quadratic form of \(A\), those two endpoint intervals contribute \(O(1)\). On the central interval, substituting \(K''=f-K^3/2\) and integrating \((K^3K')'\) produces
\[
 (Au,u)\ge \int_{\rm central}
       \bigl(K^6/6-(17/6)fK^3-f^2\bigr)dx-C .
 \tag{5}
\]
The bounded endpoint values of \(K^3K'\) account for the constant. Thus \((Au,u)\ge c_1 H\) after fixing \(H\) sufficiently large and then taking \(b\) large, while \(\|u\|^2\le C_1 H\). Disjoint blocks separated by a unit gap give \(\kappa b\) independent functions above the same positive Rayleigh quotient \(c_0\), also on their entire span.

Both \(A\) and \(B\) commute with the two commuting reflection actions on normal variations. Concretely a symmetry taking \(X(s)\) to \(X(g(s))\) acts by the pullback under \(s\mapsto g(s)\), multiplied by the constant sign with which it takes \(N(s)\) to \(N(g(s))\). The maps \(g\) are arclength isometries. In (3), the potential and \(K^2\) are even under these actions, while \(q\) has the sign of the parameter derivative, as required for \(q\partial_s\). The four group translates of the chosen open band are in distinct quarters. Extending every block with the four signed character coefficients produces the same Rayleigh quotient in each character space. The min-max principle gives at least \(\kappa b\) eigenvalues of \(A\) at or above \(c_0\) in each space.

## From a self-adjoint comparison to actual eigenvalues

Fix any one character space. Choose \(M>C+2+c_0\) in (4), independent of \(b\). The positive resolvent \(T_0=(M-A)^{-1}\) satisfies \(\|T_0\|\le1\) and \(\|T_0\|_1\le C_2b\), where the subscript 1 denotes the trace norm. Indeed (4) implies that \(T_0\) is bounded above in quadratic form by \((1+\tfrac12\partial_x^4)^{-1}\), whose full-period trace is
\[
 \sum_{n\in\mathbb Z}\frac{1}{1+\tfrac12(2\pi n/\ell_b)^4}\le C(1+\ell_b).
\]
The derivative also satisfies \(\|\partial_xT_0\|\le C\), by applying (4) to \(u=T_0h\) and interpolating. Thus \(\|BT_0\|\le C/b\). The true resolvent \(T=(M-A-B)^{-1}=T_0(I-BT_0)^{-1}\) obeys
\[
 \|T\|\le K_0,\qquad \|T\|_1\le C_3 b,\qquad
 \|T-T_0\|_1\le C_4 .
\]
For each fixed integer \(p\ge2\), telescoping the powers gives \(|\operatorname{tr}T^p-\operatorname{tr}T_0^p|\le C_p\). The min-max bound yields \(\operatorname{tr}T_0^p\ge\kappa b (M-c_0)^{-p}\).

Each nonzero eigenvalue \(\mu\) of \(T\) equals \(1/(M-\lambda)\) for an eigenvalue of \(A+B\), with the same algebraic multiplicity. For \(\operatorname{Re}\lambda<c_0/2\), one has \(|\mu|\le v=(M-c_0/2)^{-1}\). Put \(u=(M-c_0)^{-1}>v\). If \(m_b\) counts the remaining eigenvalues with multiplicity, Lidskii's formula and the trace-norm bound on the sum of absolute eigenvalues give
\[
 \kappa b u^p-C_p
       \le |\operatorname{tr}T^p|
       \le m_b K_0^p+C_3 b v^{p-1}.
\]
This argument also applies if the count is initially allowed to be infinite, in which case the desired lower bound is immediate. Choose \(p\) fixed so that \(\kappa u^p>2C_3v^{p-1}\). For all sufficiently large \(b\), \(m_b\ge\eta b\), with \(\eta>0\) independent of \(b\). Scaling (3) back proves the theorem. [Simon, Lidskii's trace formula](https://doi.org/10.1112/blms/15.2.146)

## Finite-time physical amplification

In the normal graph \(Y=X+hN\) over the fixed reference labels, \(g=|Y_s|=\sqrt{(1-kh)^2+h_s^2}\) and
\[
 h_\tau=\frac{-F_Y-Y\cdot N_Y}{N\cdot N_Y},\qquad
 N\cdot N_Y=(1-kh)/g .
\]
Its leading coefficient is \(-g^{-4}\partial_s^4h\), with all lower coefficients smooth near \(h=0\). This is a locally uniformly parabolic scalar equation on the compact label circle, including for immersed profiles with self-intersections. The inverse-function argument for quasilinear parabolic equations yields a differentiable solution map near the stationary solution on each fixed finite interval, in sufficiently regular parabolic Sobolev spaces. One can apply the local result successively about \(h=0\). Its derivative at zero solves \(h_\tau=G_bh\) with prescribed initial variation. [Mantegazza and Martinazzi, Proposition 2.3 and the proof of Theorem 1.1](https://www.numdam.org/item/ASNSP_2012_5_11_4_857_0/)

The eigenfunctions are smooth by elliptic regularity. On an unstable eigenvector the complexified derivative at \(\tau=\log3\) acts as multiplication by \(3^\lambda\). Its spectral radius, hence its operator norm, is at least \(3^{cb^2}\). Equivalently, real perturbations have this lower bound on the supremum amplification ratio in any real Sobolev Hilbert norm with its standard complexification. The profile is unchanged in normalized coordinates, and the corresponding physical time is exactly \(20\). This sensitivity alone gives no estimate for the signed motion of either support line of a perturbed curve.
