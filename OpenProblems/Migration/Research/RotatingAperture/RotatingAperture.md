# Rotation and the convex hull of a closed elastic expander

Let \(X\) be a smooth closed unit-speed plane immersion with arclength period \(L>0\), tangent \(T\), normal \(N=JT\), and signed curvature \(k\). Use the similarity centre as origin. Write \(p=X\cdot N,\ q=X\cdot T\). The normal profile equation is
\[
 F=k_{ss}+\tfrac12 k^3=-a(p+bq),\quad a>0 .
\]
Here \(b\) is the angular velocity divided by the dilation rate in logarithmic scale. Put \(r_*=(2a)^{-1/4}\) and take any \(R\) such that \(|X|\le R\) through a full period.

**Centre containment.** If \(4|b|\ge\pi(R/r_*)^2\), the similarity centre belongs to the convex hull of the profile. Thus no straight line strictly separates any two complete time slices of the corresponding flow. The conclusion allows self-intersections and all turning numbers.

**Disk containment.** For \(r\ge0\) put \(D=r/r_*\). If \(D<1\) and
\[
 \frac{\pi}{2}\left(\frac{R+r}{r_*}\right)^2(1+2|b|D)
       < 2|b|(1-D)^2 ,
\]
the whole closed disk of radius \(r\) about the centre belongs to the hull. In particular a strict margin in the centre criterion gives a nonzero disk by continuity at \(r=0\).

### The angular estimate

For an exterior viewpoint \(d\), strict separation gives a unit direction along which every point of \(X-d\) has positive projection. The polar argument in this frame has a single-valued smooth periodic branch. Subtract its midrange and call the resulting function \(\psi\). Its supremum norm is \(h<\pi/2\). Writing \(p_d=(X-d)\cdot N,\ q_d=(X-d)\cdot T,\ v=|X-d|^2\), differentiation gives \(\psi'=-p_d/v,\ p_d'=-kq_d\). Integration over one period gives
\[
 \int p_d^2/v=-\int k q_d\psi .
\]
Cauchy–Schwarz therefore gives \(\int p_d^2\le M h\,\|k\|_2\|q_d\|_2\) for any upper bound \(M\) on \(v\). These formulas are valid for an arbitrary smooth closed unit-speed immersion in the indicated half-plane.

### The profile identities

Set \(C=\int k^2,\ Z=\int(p+bq)^2,\ P=\int p^2,\ Q=\int q^2\). The periodic primitive \(q k_s-pk^2/2-k\) has derivative \(Fq\). Consequently \(p+bq\) is orthogonal to \(q\) in \(L^2\). The dilation identity \(\int Fp=-C/2\), together with \(\int kp=-L\) and \(\int kq=0\), gives
\[
 C=2aZ,\qquad P=Z+b^2 Q,\qquad L^2\le CZ,\qquad Z>0 .
\]
If the centre is exterior, the angular estimate forces \(Q>0\). Using \(P\ge2|b|\sqrt{ZQ}\) at \(d=0\) yields \(2|b|\le R^2h\sqrt{2a}\). The strict upper bound \(h<\pi/2\) proves the centre criterion, including equality in the stated threshold.

For \(|d|\le r\), the triangle inequality gives
\(\|p_d\|_2\ge \sqrt P-r\sqrt L\) and \(\|q_d\|_2\le\sqrt Q+r\sqrt L\). Since \(r\sqrt L\le D\sqrt Z\le D\sqrt P\), any exterior \(d\) in this disk must satisfy
\[
 2|b|(1-D)^2P
 \le (R+r)^2(\pi/2)\sqrt{2a}\,(1+2|b|D)P.
\]
Division by \(P>0\) finishes the disk argument.

### A second obstruction close to the circle radius

Write \(y=(R/r_*)^2\). An exterior centre would force \(x=Q/Z>0\) with
\[
   1+(1+b^2)x\le y,\qquad (1+b^2x)^2<(\pi/2)^2y^2x .
\]
The first inequality follows by integrating \(p^2+q^2=|X|^2\) and using \(L\le\sqrt{2a}Z\). The second is the strict polar estimate. In particular \(\pi^2y^2(y-1)\le4(1+b^2)\) guarantees centre containment for every rotation ratio, including zero. If \(b^2(y-2)\le1\), eliminating \(x\) in these two inequalities also guarantees containment whenever
\[
  \pi^2 y^2(y-1)(1+b^2)\le 4(1+b^2y)^2.
\]
The elimination uses the monotonic decrease of \((1+b^2x)/\sqrt{x}\) for \(0<x\le1/b^2\) when \(b\ne0\). These tests describe obstructions from the integral estimates. Attainability of their boundaries by actual profiles is a separate question.

### Verification and scope

The six project modules verify the profile identities, the polar integral estimate, the centre and time-slice conclusions, the support perturbation estimates, the explicit disk bound, and the two radius obstructions. They apply to profiles satisfying the displayed equation. Whole-curve migration of arbitrary closed free elastic flows and the classification of all closed similarity profiles remain open.

[Profile identities](../../Migration/RotatingSupportBalance.lean) · [Polar argument](../../Migration/PolarOscillation.lean) · [Centre and time slices](../../Migration/RotatingHull.lean) · [Support perturbations](../../Migration/NormTransport.lean) · [Disk bound](../../Migration/RotatingHullDisk.lean) · [Radius tests](../../Migration/RotatingRadius.lean) · [Verification record](RotatingApertureVerification.json)
