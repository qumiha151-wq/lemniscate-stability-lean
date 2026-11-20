# A universal improvement of the signed cubic half-threshold

For a smooth closed immersed planar free elastic flow, put \(E=\frac12\int k^2ds\), \(U=EL\), and
\[
 G=\sqrt L\,|\int k^3ds|/(\int k^2ds)^{3/2}.
\]
There exists a universal \(g_*<1/2\), with \(g_*>0\), such that \(\liminf_{t\to\infty}G(t)>g_*\) implies \(L(t)=O(t^{1/4})\) and \(E(t)=O(t^{-1/4})\). Every flow of turning number zero satisfies \(\liminf_{t\to\infty}G(t)\le g_*\), without an assumed energy cap. The compactness proof below gives existence. The separate finite-window proof and its consequences for the flow have also been checked in Lean. [Formal verification](ExplicitThresholdVerification.md) A separate finite-interval proof gives an explicit admissible value \(g_*=1/2-\epsilon\), with \(\epsilon>0\) specified there. [Explicit finite-interval estimate](FiniteWindowThreshold.md)

## The static estimate

Write \(R^2=L^{-1}\int k^2ds>0\). On the coordinate \(x=Rs\) set \(u=k/R\) and \(v=u''+u^3/2=F/R^3\). Denote the average over the period \(P=RL\) by a bar. Define
\[
 s_0=\bar u,\qquad h=\overline{u^3},\qquad
 e=\overline{v^2}-\tfrac12\overline{uv}.
\]
Thus \(\overline{u^2}=1\), \(G=|h|\), and \(\bar v=h/2\). We claim there is a universal \(\epsilon\in(0,1/2)\) such that every smooth real periodic \(u\) with \(\overline{u^2}=1\), \(|s_0|\le\epsilon\), and \(e\le\epsilon\) satisfies \(|h|\le1/2-\epsilon\).

Otherwise take a sequence with \(|s_0|\le1/j\), \(e\le1/j\), and \(|h|>1/2-1/j\). Change the sign of each \(u\) if needed to make \(h>0\). The exact identity
\[
 e=\overline{(v-u/4-(2h-s_0)/4)^2}+\frac{(2h-s_0)^2-1}{16}
\]
forces \(h\to1/2\), \(e\to0\), and \(\overline{(v-u/4-1/4)^2}\to0\). In particular \(\overline{v^2}\) stays bounded.

Extend the functions periodically to the real line and choose their arclength origins uniformly in their respective periods. These random translates have translation-invariant laws. On each fixed bounded interval \(I\) the expected integrals of \(u^2\) and \(v^2\) are bounded by a constant times \(|I|\). The expected integral of the squared residual \(v-u/4-1/4\) goes to zero. Bounds on the first two integrals on \(I\) bound \(\|u\|_{H^2(I)}\). Indeed the interval Gagliardo–Nirenberg inequality gives \(\|u\|_\infty\le C_I(\|u''\|_2^{1/4}\|u\|_2^{3/4}+\|u\|_2)\). From \(u''=v-u^3/2\) one obtains \(\|u''\|_2\le C(1+\sqrt{\|u''\|_2})\). These interval estimates require no endpoint conditions.

Markov's inequality and compact embedding \(H^2(I)\hookrightarrow C^1(\overline I)\) now give tightness on \(C^1_{\rm loc}(\mathbb R)\): use \(I=[-m,m]\) and make the exceptional probability smaller than \(\eta 2^{-m}\) for each \(m\). Take a weakly convergent subsequence. Its limit is invariant under every fixed translation. Testing the residual against compactly supported smooth functions, integrating \(u''\) by parts, and using \(C^1_{\rm loc}\) convergence in law shows that the limit solves
\[
 u''=-u^3/2+u/4+1/4
\]
almost surely. A countable dense set of test functions suffices. This distributional solution is classical by the equation. The evaluation \(u(0)\) has mean zero under the limiting law by uniform integrability, since its second moments along the sequence are all one. Its limiting second moment is at most one.

The quartic potential \(V(u)=u^4/8-u^2/8-u/4\) has a unique critical point, its strict minimum at \(u=1\), since \(4V'(u)=(u-1)(2u^2+2u+1)\). Conservation of \((u')^2/2+V(u)\) shows that every solution on the line is constant one or periodic. As proved below, every such solution has **strictly positive time average**. For the translation-invariant limiting law the variables \(T^{-1}\int_0^T u(x)dx\) all have expectation zero and second moment at most one. Yet they converge pointwise as \(T\to\infty\) to a strictly positive random variable. Uniform integrability gives a contradiction and proves the static estimate.

## Positive mean of the quartic oscillator

For a nonconstant orbit let \(c-r,c+r\) be its turning values, \(r>0\). Equality of the two potential values gives \(c(c^2+r^2-1/2)=1/2\). In fact \(c>0\): the positive turning value is greater than one and, when the lower turning value is negative, \(V(-x)>V(x)\) for \(x>0\), so the positive turning value exceeds the magnitude of the negative one. Thus \(0<c<1\) and \(r^2=1/(2c)+1/2-c^2\). Put \(d=2c^2+r^2-1>0\), where positivity also follows from \(d=c^2+(1-c)/(2c)\). At energy \(H\) one has the factorisation
\[
 8(H-V(z))=(r^2-(z-c)^2)((z+c)^2+d).
\]
Change variables to \(z=c+r\cos\theta\) in the integral for the period mean. Its sign is the sign of the integral of \(z/\sqrt{(z+c)^2+d}\) over \(\theta\in[0,\pi]\). Pair the two offsets \(+y,-y\), \(0\le y\le r\). For \(y\le c\) the pair is positive except possibly at an endpoint. For \(y>c\), comparison of the squared positive and negative contributions has numerator
\[
 (c+y)^2((2c-y)^2+d)-(y-c)^2((2c+y)^2+d)
 =4cy(4c^2+r^2-1-y^2).
\]
If \(c\ge1/2\) this is nonnegative and the integral is strictly positive.

For \(0<c\le1/2\) write \(y=\cos\theta\) on \(0\le\theta\le\pi/2\), \(t=c^2/r^2\), \(a=d/r^2\), \(Q=4t+y^2+a\), and \(\Delta=Q^2-16t y^2\). Put
\[
 W=(Q+4\sqrt t\,y)^{-1/2}+(Q-4\sqrt t\,y)^{-1/2},\qquad H_1=1-\frac{4y^2}{Q+\sqrt{\Delta}} .
\]
The two inverse square-root weights have difference divided by sum equal to \(-4\sqrt t\,y/(Q+\sqrt\Delta)\); thus the paired numerator integral equals \((c/r)\int_0^{\pi/2} W H_1\,d\theta\).

Let \(z=c-2c^3\). The maximum of \(z\) on this range is \(2/(3\sqrt6)<3/11\), so \(4/7\le a=(1-z)/(1+z)\le1\) and \(t=2c^3/(1+z)\le1/4\). In particular \(Q\le3\). Convexity of \(x\mapsto x^{-1/2}\) gives \(W\ge2/\sqrt Q\ge8/7\), while \(Q\pm4\sqrt t\,y=(y\pm2\sqrt t)^2+a\) gives \(W\le\sqrt7\le8/3\). The identity \(\Delta-(a+y^2-4t)^2=16ta\ge0\) yields \(Q+\sqrt\Delta\ge2(a+y^2)\). Hence
\[
 H_1\ge b_0(\theta)=\frac{4-7\cos^2\theta}{4+7\cos^2\theta}.
\]
By substituting \(x=\tan\theta\), \(\int_0^{\pi/2}b_0\,d\theta=\pi(2/\sqrt{11}-1/2)>\pi/10\). Its negative part has support in \([0,\pi/4]\) and is bounded by \(3/11\). Putting the two weight bounds together gives
\[
 \int_0^{\pi/2}WH_1\,d\theta
 \ \ge\ \frac87\int b_0-\left(\frac83-\frac87\right)\int(b_0)_-
 \ >\ \frac{8\pi}{70}-\left(\frac83-\frac87\right)\frac{3\pi}{44}
 =\frac{4\pi}{385}>0.
\]
This proves the required positive mean at every nonconstant energy.

## Application to the free elastic flow

The first variations \(E'=-\int F^2ds,\ L'=\int kFds\) give \(U'=-L^2R^6 e\). The signed turning integral \(S=\int kds\) is constant, \(s_0=S/\sqrt{2U}\), and \(L^2 R^6=(2U)^3/L^4\). [Miura and Wheeler, §§2–3](https://arxiv.org/html/2404.12619v3)

Take \(g_*=1/2-\epsilon\). If \(\liminf G>g_*\), then \(G>g_*\) for all sufficiently late times. Whenever \(U\ge S^2/(2\epsilon^2)\) at those times, the static estimate implies \(e>\epsilon\), hence \(U'<0\). Continuity and the first-crossing argument bound \(U\) along the whole flow. The quarter-power estimates follow from the proved equivalence between bounded \(EL\) and the length and energy bounds. [Lean growth equivalence](../../LengthGrowth/ActualFlow/GrowthEquivalence.lean)

When \(S=0\), the same argument gives \(e>\epsilon\) on the entire tail. The lower bound \(2U\ge4\pi^2\) gives \(U'\le-\epsilon(4\pi^2)^3L^{-4}\). The quarter-power upper bound makes \(\int^\infty L^{-4}dt\) divergent, contradicting \(U\ge2\pi^2\). This proves the turning-zero assertion. The general upper bound for flows whose signed cubic moment can cancel remains open.

The same static estimate applies to the centered moment \(J=|2h-s_0|\). If \(\liminf J>1-\epsilon/2\), the barrier \(U=S^2/(2\epsilon^2)\) gives an eventual upper bound depending only on the turning number, and excludes turning number zero. Combined with dynamical rigidity, this yields \(\liminf J\le1\) for every closed flow, with equality precisely for smooth convergence of the normalized curve to a round circle of its covering number. Each fixed nonzero turning number admits a positive gap below one for flows without this convergence. [Centered moment rigidity](CriticalMomentRigidity.md)
