# An exterior optimal similarity centre with vanishing relative force error

Let \(Y\) be a smooth closed regular plane immersion parametrized by arclength, \(T\) its unit tangent, \(N=JT\), \(k\) its signed curvature, and \(F=k_{ss}+k^3/2\). Its actual elastic-flow velocity has normal component \(-F\). Consider the least-squares fit
\[
 \min_{a,b\in\mathbb R,\;v\in\mathbb R^2}
 \|F+(aY+bJY+v)\cdot N\|_{L^2(ds)} .
\]
There is a sequence of such immersions for which the minimizer is unique, \(a>0,\ b=0\), the minimizing centre \(C=-v/a\) lies strictly below the entire image, and the minimum divided by \(\|F\|_2\) tends to zero. If \(h=Y\cdot e_y\), the ratio
\[
 \frac{\min\bigl((C+3(Y-C))\cdot e_y\bigr)-\max h}
      {\max h-\min h}
\]
exceeds \(1/4\). This estimates an instantaneous similarity fit. Establishing half-plane migration for the subsequent actual flow requires a dynamical argument.

## The underlying sequence and its limiting measures

Use the matched, coefficient-one reflected pure expanders \(X_j\) with central derivative \(b_j=k_s(0)\to+\infty\). Denote quarter length by \(s_j\), length by \(L_j=4s_j\), maximum radius by \(R_j\), and bending energy by \(E_j=\frac12\int k^2ds\). The matching construction and its limit estimates give
\[
 s_j/\sqrt{b_j}\to\tau_*,\qquad R_j/\sqrt{b_j}\to z_*=\gamma\tau_*>0,
 \qquad E_jL_j/b_j^2\to32 .
\]
In particular \(\sqrt{E_j/L_j}\asymp R_j\). On every fixed \(0\le\tau=s/\sqrt{b_j}\le B<\tau_*\), the scaled position \(X_j/\sqrt{b_j}\) converges uniformly to \(\gamma\tau e_0\), and the scaled stress \(W=(k^2T/2+k_s N)/b_j\) tends to \((1-\tau^2/\tau_*^2)e_0\). The matching selects the near-turn seam with the displayed length limit. These statements concern that sequence. [Physical matching](../../../SolitonClassification/Research/ReflectedScattering/PhysicalSeamMatching.md) · [Limit statements](../../../SolitonClassification/Research/ReflectedScattering/IndependentMatchingAudit.md) · [Outer averaging](../../../SolitonClassification/Research/ReflectedExpanders/LargeMarkerNecessaryBounds.md)

The slow arclength remaining after \(B\) is at most \(\tau_*-B+o(1)\). Thus the first quarter converges in Hausdorff distance after division by \(R_j\) to \([0,e_0]\), and its endpoint tends to \(e_0\). At the seam \(X_j\cdot T=0\), and the second quarter is its reflection in the axis through zero and the seam. The other half is its central inversion. Choose coordinates for each \(j\) putting the exact seam axis on the horizontal line, with positive first tip. The coordinate rotation tends to a fixed rotation, the two coordinate reflections preserve the full curve, and the scaled image tends to \([-1,1]\times\{0\}\).

Set \(P_N=N\otimes N\). In those coordinates the pushforwards under \(X_j/R_j\) converge weakly, with the measures on the right supported on the segment:
\[
 \frac{ds}{L_j}\rightharpoonup \frac{dx}{2},\qquad
 P_N\frac{ds}{L_j}\rightharpoonup (I+e_x\otimes e_x)\frac{dx}{6}.
 \tag{1}
\]
On each compact pre-turn interval the stress direction tends to \(e_x\). In the stress frame the normal components are \(w=U'\) and \(u=U^2/2\), where \(U''=-U^3/2,\ U(0)=0,\ U'(0)=1\). Over its period \(\langle w^2\rangle=2/3,\ \langle u^2\rangle=1/3,\ \langle wu\rangle=0\). The last quantity is the average of \((U^3/6)'\). For each component subtract its period mean and take a periodic primitive divided by the square root of the scaled stress magnitude. Differentiation along the slow dynamics gives the zero-mean term times \(b_j\), with uniformly bounded error on compact pre-turn intervals. Test by smooth functions of scaled position, integrate by parts and use uniform approximation for continuous tests. The position there advances linearly in slow time. The four reflections preserve the limiting diagonal matrix and the remaining slow arclength vanishes as \(B\uparrow\tau_*\). This gives (1).

For any fixed \(D>0\), small \(\delta>0\) and \(j\) sufficiently large depending on \(\delta,D\), define
\[
 S_{j,\delta}=\{s:|\mathop{\rm Re}X_j(s)|/R_j>1-D\delta\}.
\]
There is a constant \(K_D\), independent of \(\delta,j\) in this order of limits, such that
\[
 |S_{j,\delta}|\le K_D\delta L_j,\qquad
 |k_s|+k^2\le K_D\delta R_j^2\quad\hbox{on }S_{j,\delta}.
 \tag{2}
\]
Choose a slow time \(\tau_*-K\delta\) with \(K\) large depending only on \(D\). The compact pre-turn convergence excludes the indicated set before this time. There the scaled stress has magnitude \(O_D(\delta)\). The remaining slow length is \(O_D(\delta)\), and the exact equation \(W_\tau=-((X_j/\sqrt{b_j})\cdot N)N\) bounds its speed uniformly. This controls the stress throughout the tip and hence proves (2). The same speed estimate from initial time gives the global bound \(|k_s|+k^2=O(R_j^2)\).

## Regression after a conformal change

Let \(H\) be a real even polynomial and \(f(z)=z+iH(z)\). Since \(f'(x)=1+iH'(x)\), its derivative is nonzero in a complex neighborhood of the segment. Define \(Y_j=R_j f(X_j/R_j)\). These curves are regular for sufficiently large \(j\) and reflect about the vertical axis. Bars denote their geometry. Write \(G=\int P_{\bar N}\,d\bar s\), which is positive definite because a closed regular curve cannot have all tangents parallel. The translation and dilation virials are
\[
 \int\bar F\bar N\,d\bar s=0,\qquad
 -\int\bar F(Y_j\cdot\bar N)\,d\bar s=\bar E>0.
\]
Reflection and uniqueness give zero rotation, zero horizontal translation, and a best dilation centre on the vertical axis. Indeed reflection conjugates \((a,b,v_x,v_y)\) to \((a,-b,-v_x,v_y)\) and leaves the objective invariant. Uniqueness follows from positive definiteness of the four-parameter Gram matrix on any nonround closed regular curve. A kernel vector would generate a similarity vector field tangent everywhere, whose full flow preserves the compact image by integrating its induced smooth tangential field on the parametrizing circle. Expansion and translation cannot preserve a bounded nontrivial compact image. A nontrivial rotation would make the radius constant along the curve wherever it is positive, and hence everywhere, giving a circle. These curves have turning number zero, since \(f'\) has a smooth logarithm in a simply connected tube about the segment and \(X_j\) has zero turning number. They therefore cannot be round.

Eliminating the translation variables yields
\[
 GC_j=\int P_{\bar N}Y_j\,d\bar s,\qquad
 a=\frac{\bar E}{\int((Y_j-C_j)\cdot\bar N)^2\,d\bar s}>0 .
\]
The conformal factor rotates each normal by the phase of \(f'\) and multiplies arclength by \(|f'|\). For \(t=(1,H')/\sqrt{1+H'^2}\), (1) therefore gives limiting weighted projection \((I+t\otimes t)d\ell/6\) on the graph \(\Gamma=(x,H(x))\), \(d\ell=\sqrt{1+H'^2}\,dx\). Evenness makes the integrated matrix diagonal. In particular
\[
 \lim_{j\to\infty}\frac{C_{j,y}}{R_j}=
 \frac{\displaystyle\int_{-1}^1
       \frac{H(1+2H'^2)+xH'}{\sqrt{1+H'^2}}\,dx}
      {\displaystyle\int_{-1}^1
       \frac{1+2H'^2}{\sqrt{1+H'^2}}\,dx}.                    \tag{3}
\]
The scaled height extrema tend to the extrema of \(H\) by Hausdorff convergence.

## Positive normalized separation

Choose \(g\in C_c^\infty((0,3))\), \(0\le g\le1,\ \max g=1\), with
\[
 J=\int\frac{g'}{\sqrt{1+g'^2}}\,du<-0.64 .
\]
A triangular tooth first rises at slope \(4\) over length \(1/4\), then descends at slope \(-1/2\) over length \(2\), giving \(J=1/\sqrt{17}-2/\sqrt5<-0.65\). Translate inside \((0,3)\), convolve with a nonnegative compactly supported smooth kernel, and normalize by its maximum. Dominated convergence preserves the strict bound for a narrow kernel.

For \(x>0\), put \(H_\delta(x)=\delta g((x-1+4\delta)/\delta)\) and reflect evenly. Its support consists of two bands in \(|x|>1-4\delta\). Its derivatives of orders one to four are \(O(1),O(\delta^{-1}),O(\delta^{-2}),O(\delta^{-3})\). Choose a real even polynomial \(H\) with \(\|H-H_\delta\|_{C^4[-1,1]}\le\delta^3\), by uniform polynomial approximation of the fourth derivative, integration with matching lower jets, and symmetrization.

In (3) the \(H\) term contributes \(O(\delta^2)\). Each tip contributes \(\delta J+O(\delta^2)\) from \(xH'/\sqrt{1+H'^2}\). The denominator is \(2+O(\delta)\). These bounds include the polynomial approximation error. Thus, at fixed \(\delta\), the limiting scaled centre is \(\delta J+O(\delta^2)\), and the limiting minimum and maximum heights are \(O(\delta^3)\) and \(\delta+O(\delta^3)\). As first \(j\to\infty\) and then \(\delta\downarrow0\), the tripled-image gap divided by the original width tends to
\[
 -2J-1>0.28.
 \tag{4}
\]

## Full force estimate and diagonal choice

Write \(f'(X_j/R_j)=e^{\omega+i\beta}\). The exact transformation laws are \(d\bar s=e^\omega ds,\ \bar k=e^{-\omega}(k+\beta_s)\). Set \(A=k+\beta_s\). Differentiation gives
\[
 \bar F=e^{-3\omega}
 [A_{ss}-3\omega_sA_s+(2\omega_s^2-\omega_{ss})A+A^3/2].
 \tag{5}
\]
For \(q=\log f'\) and \(z=X_j/R_j\), the three chain rules are
\[
 (q(z))_s=q'T/R_j,\quad (q(z))_{ss}=q''T^2/R_j^2+q'ikT/R_j,\quad
 (q(z))_{sss}=q'''T^3/R_j^3+3q''TikT/R_j^2+q'(ik_s-k^2)T/R_j .
\]
For each fixed polynomial and \(\delta\), Hausdorff convergence transfers its bounds through four derivatives from the segment to the actual curve with arbitrarily small additive tolerance. Precisely, project \(\mathop{\rm Re}z\) to \([-1,1]\) and apply uniform continuity near that interval. Off \(S_{j,\delta}\) with \(D=5\), \(f-\mathrm{id}\) and all derivatives through order four are \(O(\delta^3)\). Everywhere \(|f'|\) is between two absolute positive constants, and the bounds on \(f'',f''',f''''\) on the tip are \(O(\delta^{-1}), O(\delta^{-2}), O(\delta^{-3})\). The same bounds apply successively to \(q',q'',q'''\).

Using (2) in (5), the largest curvature-derived tip term is bounded by \(C(|k_s|+k^2)/(\delta R_j)\le CR_j\). The remaining derivative terms are bounded by \(C|k|/(\delta^2R_j^2)+C/(\delta^3R_j^3)\le CR_j\) for large \(j\) at fixed \(\delta\). Since \(F=-X_j\cdot N\), globally \(|F|\le R_j\). Off the tip, \(e^{-3\omega}-1\), the frame rotation, and the change of scaled position are \(O(\delta^3)\). Globally \(Y_j=O(R_j)\). We conclude both
\[
 |\bar F-F|+|\bar F+Y_j\cdot\bar N|
 \le
 \begin{cases}
 C\delta^3 R_j,&s\notin S_{j,\delta},\\
 CR_j,&s\in S_{j,\delta}.
 \end{cases}                                                     \tag{6}
\]
Here \(F,\bar F\) are evaluated at corresponding material labels. The dilation virial for the reference profile gives \(\|F\|_2^2=E_j\). By (2), (6), and uniform equivalence of the two arclength measures, \(\|\bar F\|_{L^2(d\bar s)}\asymp R_j\sqrt{L_j}\) and the relative error at \(a=1,b=0,v=0\) is \(O(\sqrt{\delta})\). The minimum is at most that large.

Finally take any \(\delta_n\downarrow0\) sufficiently small and make the stated polynomial choice at each \(n\). Then choose one matched index \(j(n)\) large enough for (2), (6), for the scaled vertical centre and both scaled extrema to differ from their fixed-\(\delta_n\) limits by at most \(\delta_n^2\), and for \(j(n)>j(n-1)\). The resulting sequence satisfies (4), with an error tending to zero, and its best-fit relative defect vanishes. Discarding finitely many terms gives the asserted strict margin on every member.
