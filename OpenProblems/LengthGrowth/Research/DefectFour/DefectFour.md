# A forward-invariant bending sublevel with defect four

For a single smooth immersed closed planar free elastic flow put \(B=\int k^2\,ds\), \(U=LB\) and \(d=U-4\pi^2\). If \(d(0)\le4\), then \(U\) is nonincreasing for the entire flow and it decreases strictly at every noncircular slice. In particular:
 
* \(L(t)\le\max\{2L(0),(4U(0)^2 t)^{1/4}\}\) for the physical flow \(X_t=-(k_{ss}+k^3/2)N\).
* Every closed similarity solution meeting this sublevel is a singly covered circle.
* The convex hull at every later time contains the earlier arclength centroid. A quantitative common disk is proved in the [independent migration project](../../../Migration/Research/DefectFour/FixedDisk.md).

Novaga proves non-migration up to defect \(8/3\) and derives the exact signed evolution and Fourier identities used here. The enlarged range uses a second application of the closure estimate, removal of the constant part of \(u^2\) before estimating the fourth-order term, and a uniform rational estimate. The global statements outside this sublevel remain open. [Novaga, §§2–4](https://arxiv.org/html/2611.07242v1)

## One normalized time slice

Turning is \(+1\) after an orientation choice, by Novaga's Lemma 2.2 since \(4<8\pi^2/3\). At a fixed time dilate to \(L=2\pi\), put \(u=k-1,\ x^2=V=\int u^2=d/(2\pi)\), \(X=\|u_{ss}\|_2,\ Q=\int u_s^2\), and \(W=V/(2\pi)\). For \(V>0\), use \(t=(X/\sqrt V)^{-1/2}\); in this section \(t\) labels a spectral ratio, not flow time. Write \(T=e^{i\alpha+is+i\phi}\), with \(\phi_s=u\) and zero mean. If \(V_1\) is the part of \(V\) in harmonics \(j=\pm1\), closure and Parseval give
\[
 V_1\le\|\phi\|_2^4/(4\pi),\qquad
 \|\phi\|_2^2\le V/4+3V_1/4.
\]
First use \(\|\phi\|_2^2\le V\), giving \(\|\phi\|_2^2/V\le1/4+3V/(16\pi)<29/100\). Reinsert this value in the first inequality and use the second again. The result is \(\|\phi\|_2^2/V<13/50\), and \(V_1\le (13/50)^2 V^2/(4\pi)\). The first pair of curvature harmonics has sup norm at most \((13/50)W\). The nonzero frequencies outside this pair have absolute index at least two. Hence \(X^2/V\ge16-15V_1/V\) and \(Q/V\ge4-3V_1/V>3\). These imply \(0<t<501/1000,\ 0<x<4/5\). The same Fourier argument giving Novaga's two sup norm bounds now gives, for \(M=\|u\|_\infty,\ g=tM\),
\[
 g\le x(227/500+(17/500)t),\qquad
 gt\le x(81/500+(17/500)t^2).
\]
Indeed the higher-mode terms before multiplication by \(t\) are at most \((227/500)\sqrt Q\) and \((81/500)X\), respectively; \(Q\le X\sqrt V\). The correction to each is \((13/50)W\), and \((13/50)W/x<17/500\). [Fourier estimates underlying these inequalities](https://arxiv.org/html/2611.07242v1#S3)

## Retaining the mean-free quadratic term

Write \(I_j=\int u^j,\ S=\sqrt{I_4}/X=tb\) and \(p=\|u^2-W\|_2/X\). Then \(0\le b\le g\) and
\[
 p^2=S^2-Wt^4\le (tb)^2-(7/44)x^2t^4 .
\]
In taking the norm of \(u_{ss}+(3u^2+u^3)/2\), first project onto the space of mean-zero functions. The norm of the projected nonlinear term is bounded by \(X A\), where \(A=3p/2+gb/2\). The removal of the mean of \(u^2\) matters for the lowest possible frequencies.

Use a dot for the doubled-speed flow \(X_{\rm pos}'=-(2k_{ss}+k^3)N\), the normalization in Novaga. In his exact signed identity (3.6), the terms \(W(6V-2Q)\) have nonpositive sum. The cubic coefficient has magnitude at most 16. Using \(|I_3|\le\sqrt{V I_4}\) and \(5-W>489/100\) gives, whenever \(A\le1\),
\[
 \frac{\dot U}{LX^2}\le
 -4(1-A)^2+q+16t^3b-\frac{489}{100}(tb)^2,\qquad
 q=(10Q-8V)/X^2\le\min(2,10t^2-8t^4).
\]
The bound by 2 follows modewise from \(2(j^2-1)(j^2-4)\ge0\) for nonzero integer \(j\). The other bound uses \(Q\le X\sqrt V\). [Signed identity and normalization](https://arxiv.org/html/2611.07242v1#S3)

## Uniform bound with exact rational arithmetic

Split \([0,501/1000]\) into 64 equal intervals \([l,h]\). Set \(v=\min(227/500,81/(500l))+(17/500)h\), omitting the second entry of the minimum at \(l=0\). Then \(b\le g\le xv\). Let \(H\) be the upper rational rounding of \(\sqrt{v^2-(7/44)l^2}\) to a millionth, \(B_*=(4/5)v,\ A_*=(6/5)hH+B_*^2/2\). The different uses of the symbol \(B_*\) here and of the bending energy \(B\) are local to their stated formulas.

The projection bound gives \(p\le txH\). Because \(gb\le B_*b\), one has \(A_*-A\ge (B_*^2-b^2)/4\). The rational input checks give \(A_*\le27/100\). Consequently
\[
 4[(1-A)^2-(1-A_*)^2]\ge \tfrac75(B_*^2-b^2)
 \ge \tfrac{489}{100}\big[(lB_*)^2-(tb)^2\big].
\]
This retains the negative quartic contribution even when \(b\) is small. The upper bound on \(\dot U/(LX^2)\) is therefore at most
\[
 -4(1-A_*)^2+\min(2,10h^2-8l^4)+16h^3 B_*-\tfrac{489}{100}(lB_*)^2.
\]
This is at most \(-1/40\) on every one of the 64 intervals, including both endpoints. The rational tests and their implication for every real spectral ratio in the interval have Lean proofs. [Exact inputs](../../LengthGrowth/ActualFlow/DefectFourBins.lean) · [Continuous inequality](../../LengthGrowth/ActualFlow/DefectFourBarrier.lean)

## Forward invariance and the three questions

For the physical half-speed convention the normalized bound is \(U'/(LX^2)\le-1/80\) on noncircular slices. Scaling back preserves its sign. If \(V=0\) the curve is a singly covered circle and \(U'=0\). At a first exit from \(U\le4\pi^2+4\) the boundary value corresponds to \(V>0\), and its derivative is strictly negative; continuity excludes exit. The scalar \(U\) is thus nonincreasing. Self-similarity preserves \(U\), forcing \(V=0\) on any similarity solution in the sublevel.

For length put \(E=B/2,\ D=\int(k_{ss}+k^3/2)^2\,ds\). Then \(|L'|^2\le2ED=-(E^2)'\). When \(L(t)>2L(0)\), take the last earlier time \(s\) with \(L(s)=L(t)/2\); integration gives \(L(t)/2\le E(s)\sqrt{t-s}\le U(0)\sqrt t/L(t)\). This proves the stated bound. The earlier [single-flow length project](../../STATUS.txt) records further estimates without the low-defect assumption.

The real-variable and rational coercivity steps are kernel-checked. The Fourier reductions and attachment of this signed bound to the physical evolution and the sublevel conclusions above are supplied as mathematical arguments. The scope of the separate hull verification is recorded in the linked migration project.
