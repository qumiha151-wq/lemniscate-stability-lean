# Elastic force at two inflections of the same closed expander

Fix the dilation coefficient to one. Let a smooth closed zero-turn profile cross its dilation centre with zero curvature and positive curvature derivative \(b\). For all sufficiently large \(b\), on this same profile there are simple inflections \(s,t\) with
\[
  k(s)=k(t)=0,\qquad F(s)<-\sqrt b/1200,qquad F(t)>\sqrt b/1200,
  \qquad F=k_{ss}+k^3/2.
\]
Consequently, given any error bound, there is one closed profile on which **every** scalar law \(G(k)\) incurs an error larger than the prescribed bound, even when \(G\) can be chosen separately for that profile. The discrepancy already occurs at zero curvature. [Lean statements and proofs](../../SolitonClassification/ForceAtInflections.lean)

In the slow variable \(u=s/\sqrt b\), the descent estimates give stress-direction component \(a>1/1200\) on \([1/2,1]\) for sufficiently large \(b\). The oscillator angle increases by at least \(b/16\) between the two endpoints. Its continuous lift therefore crosses two levels \(2n\pi\) and \((2n+1)\pi\) with an integer \(n\). At both levels the scaled curvature \(K\) vanishes and the amplitude stays positive, giving simple curvature zeros. The curvature derivative divided by the stress amplitude, in the scaled variables, equals \(+1\) and \(-1\), respectively. The identity \(a=((K^2/2)q+Vp)/A\) then makes the rescaled normal support \(p\) equal to \(+a\) and \(-a\), respectively. Returning to physical arclength multiplies the support by \(\sqrt b\). The coefficient-one expander equation gives \(F=-X\cdot N\), with the stated opposite signs. [Critical layer](../../SolitonClassification/CentreCriticalLayer.lean) · [Initial winding estimate](../../SolitonClassification/CentreShotWinding.lean)

Arbitrarily high centre markers occur on actual closed profiles by the existence theorem. Whichever real number \(G(0)\) is assigned, one of these two inflections gives an error greater than \(\sqrt b/1200\). This obstruction concerns laws using only the current signed curvature. [Closed profile existence](../../SolitonClassification/UnboundedClosedExpanders.lean)

## Finitely many possible forces at the same curvature

Fix a nonnegative integer \(n\) and a finite tolerance \(M\). There is a normalized closed zero-turn expander on which any choice of \(n\) functions \(G_i(k)\) incurs error greater than \(M\) for **all** of the functions at one simple inflection. One may choose the functions separately for each profile. Once they have been chosen, the inflection can be found within any positive period starting at the marked centre crossing. The forces are in the physical arclength coordinates for dilation coefficient one.

For the first \(\sqrt b/2\) units of arclength from the centre marker, any two curvature zeros \(s\le t\) obey
\[
               |F(t)|-|F(s)|\ \ge\ (t-s)/72.
\]
In the slow coordinate \(u=s/\sqrt b\), the quantity \(18a+\delta Uw-u/4\) is nondecreasing on \([0,1/2]\), where \(a\) is the component of position along the normalized stress, \(U,w\) are the normalized oscillator coordinates, and \(\delta=1/b\). It starts at zero. At every curvature zero the term \(Uw\) vanishes, and the support equation gives \(a=|F|/\sqrt b\). Applying monotonicity at the two zeros proves the bound. Together with the early inflection count, it gives at least \(\lfloor b/(4608\pi)\rfloor\) different force magnitudes at the single curvature value zero within every positive period. [Monotonicity](../../SolitonClassification/CentreShotAlignment.lean) · [Force separation and the count](../../SolitonClassification/InflectionForceBranches.lean)

To obtain arbitrarily large approximation error for a fixed number of branches, choose \(n+1\) disjoint slow-time subintervals of \((0,1/576]\) with positive gaps between them. The angle gained on each subinterval is at least \(b/8\) times its width. For sufficiently large \(b\) this exceeds \(\pi\), so every subinterval contains a simple curvature zero. Arclength gaps between these zeros grow like \(\sqrt b\). Take them larger than \(144(1+\max(0,M))\). The signed forces there have pairwise distances greater than \(2M\), since even their magnitudes have this separation. For \(M\ge0\) each number \(G_i(0)\) can approximate at most one of those \(n+1\) forces within \(M\). This proves the assertion for every \(M\). [Separated zeros](../../SolitonClassification/SeparatedEarlyInflections.lean) · [Finite-branch approximation theorem](../../SolitonClassification/FiniteForceLaw.lean)
