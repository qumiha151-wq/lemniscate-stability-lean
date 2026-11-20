# Centre shots up to the first transition layer

Normalize the physical dilation coefficient to one. A shot starts at the centre with curvature zero and curvature derivative \(b>0\). Write \(\delta=1/b\), use slow arclength \(\tau=s/\sqrt b\), and use the outer coordinates of [the support equations](../../SolitonClassification/OuterStressOrbit.lean). The scaled position has components \(p,q\) along the normal and tangent. The stress has magnitude \(A=r^2=\sqrt{(K^2/2)^2+V^2}\). The components of position along and perpendicular to the stress are denoted by \(a,b_\perp\). The normalized oscillator coordinates satisfy \(u=U^2/2\), \(u^2+w^2=1\).

## Start directly from the centre

The actual differential equations give \((p^2+q^2)'=2q\) and \((A^2)'=-2Vp\). Differentiating \(\sqrt{\varepsilon+p^2+q^2}\) gives a derivative of absolute value at most one. Integrate from zero and take \(\varepsilon\downarrow0\). This gives \(|Z(\tau)|\le\tau\). In the same way the derivative of \(\sqrt{\varepsilon+A^2}\) has absolute value at most \(|p|\le\tau\). Since \(A(0)=1\), we obtain \(A(\tau)\ge1-\tau^2/2\) for every \(\tau\ge0\). In particular \(r\ge1/2\) on \([0,1]\). On this interval the true lifted oscillator angle winds by at least \(b/8\) when \(b\ge32\). [Physical winding theorem](../../SolitonClassification/CentreShotWinding.lean)

At \(\tau=1/2\) the longitudinal component satisfies \(a\ge1/288\). To verify this, write \(v=r/\delta+Up/(2r^2)\) for the phase speed in oscillator time. On \([0,1/2]\) the preceding bounds imply \(1/4\le\delta v\le3\), and \(a'=u-pu b_\perp/r^2\ge u/2\). The bounded function \(Uw\) satisfies \((Uw)'=(1-3u^2)v\). It follows that \(18a+\delta Uw-\tau/4\) is nondecreasing. It starts at zero, and \(|Uw|\le2\), yielding the claimed positive lower bound. The existing polynomial correction \(J\) for the transverse component starts at zero and satisfies \(|J'|\le C\delta\) on this interval. Thus \(|J(1/2)|+|b_\perp(1/2)|\le C'\delta\), uniformly in \(b\). The same slice satisfies \(1/2\le A\le3/2\). All constants are independent of the shooting parameter. [Alignment](../../SolitonClassification/CentreShotAlignment.lean) · [Physical entry data](../../SolitonClassification/CentreShotEntry.lean)

## Continuation to a shrinking stress scale

Fix \(\alpha=1/1200\) and a slow-time horizon of \(10000\). The radius bound already proved controls both position components on this whole interval. Write \(H\) for the corrected stress amplitude. On a segment where \(A\le2\), \(a\ge\alpha\), and \(r^3\ge L\delta\), taking \(L\) sufficiently large gives

\[
  \frac{15}{16}A\le H\le\frac{17}{16}A,\qquad
  H'\le-\frac{\alpha}{3},\qquad
  |J'|\le C\delta/A^2.
\]

These estimates use the polynomial remainders on one compact box. Integrating the transverse error against decreasing \(H\) gives a constant \(C_1\) independent of \(L,\delta\) such that \(|b_\perp|r^3\le C_1\delta\). Increase \(L\) so that \(C_1/L\le10^{-12}\).

The exact identity \(q=ua-wb_\perp\) then implies \((|Z|^2)'=2q\ge-2\cdot10^{-12}\). Consequently the radius squared can lose at most \(2\cdot10^{-8}\) before the horizon. It starts the descending segment at a radius at least \(1/288\). Since \(a^2+b_\perp^2=|Z|^2\), \(a\) stays strictly above \(\alpha\) while the descent estimates hold. The bound \(15A/16\le H\le H(1/2)\le (17/16)(3/2)\) simultaneously keeps \(A<2\). A first exit from either bound before hitting \(r^3=L\delta\) is therefore impossible. Remaining above this stress threshold all the way to \(10000\) would drive positive \(H\) below zero. The first threshold crossing consequently occurs on \([1/2,10000]\) for every sufficiently large fixed \(L\) and every \(0<\delta\le1/(32L)\).

At this first crossing the physical radius is \(\sqrt b\,|Z|\), with \(1/1200<|Z|\le10000\). In the instantaneous radial normalization the stress magnitude and raw impact satisfy

\[
  \mathcal A^3 |Z|^2 = L^2,\qquad
  |\mathcal I|^3 |Z|^4 = L|b_\perp|^3\le C_1^3/L^2 .
\]

The Lean theorem also gives \(\tau\ge1\) and a phase at the stopping time of at least \(b/8\). Along the segment following slow time one, \(r^3\ge L\delta\) and both position components stay bounded by the fixed time horizon. The phase integrand stays nonnegative there. [Radial-distance estimate](../../SolitonClassification/OuterRadiusBarrier.lean) · [Integrated descent](../../SolitonClassification/OuterDescentBudget.lean) · [First critical layer for the physical initial-value problem](../../SolitonClassification/CentreCriticalLayer.lean)

This estimate supplies entrance to the layer for the actual centre shots. Convergence of lengths, energies and curvature-zero counts with exact asymptotic constants uses additional averaging information. Reconstruction of closed profiles also requires matching the incoming states to the returning seam family.

## Continuity of the level crossing

The critical-layer estimates do not require the stopping time to depend continuously on the marker. To select a continuous branch on a fixed physical height \(H\), use the interval from slow time one to the critical stopping time for each separate shot. The corrected physical height starts above \(H\) and ends below it. At every crossing its derivative in forward physical arclength is strictly negative. Indeed, normalize the position radius to one at the instant of crossing. The frozen derivative bound holds uniformly in phase and direction as soon as the normalized stress magnitude is at least 12. All possible normalized crossing states at this fixed \(H\) lie in a compact stress band. Continuity gives a common margin for all sufficiently small positive radius parameters. The exact physical scaling multiplies the signed derivative by a positive clock factor. [Physical rate in an arbitrary compact stress band](../../SolitonClassification/CentreTransversality.lean)

Two downward transverse crossings in one interval would force a subsequent rise from below the level to above it. The first intervening hit disagrees with the strict sign just to its left. This proves uniqueness on the chosen flight. For continuity in the marker, every compact segment ending strictly before the first hit has positive height difference. Joint continuity and compactness preserve this strict inequality for nearby markers. Just after the selected hit, there are arbitrarily near times with negative height difference, also persisting for nearby markers. These two bounds trap the neighboring first hits to either side of the original one with arbitrarily small separation. The argument applies separately at each marker and uses no continuity of the terminal stopping time. [Continuous first-crossing theorem](../../SolitonClassification/FirstTransverseCrossing.lean)

The continuous selector applies to the actual solution with initial data \((0,b,0,0)\). There are constants \(K>0\) and \(H_0\ge17\) such that at each height \(H\ge H_0\), all sufficiently large \(b\) have a unique incoming crossing on the segment from slow time one to the first critical layer. Its time lies strictly inside the segment and depends continuously on \(b\). At that crossing the normalized stress root is at least four and the transverse impact has magnitude at most \(K/H\). The pointwise bounds on the entire segment also control the physical inverse radius and preserve the lower phase estimate \(b/8\). [Physical first-crossing selector](../../SolitonClassification/PhysicalCentreSelector.lean) · [Physical winding on the segment](../../SolitonClassification/PhysicalIncomingWinding.lean)

## Counting shooting markers

On the common physical section the centre phase lift obeys \(\theta(b)\ge b/8\), and the seam phase lift is bounded in absolute value by a fixed \(M\). Choose integers \(a,d\ge0\) with \(2\pi a>\theta(B)+M\) and \(2\pi d>2M\). The target winding levels \(2\pi(a+di)\), for \(0\le i<N\), then admit disjoint centre-phase windows. Set \(C=8(2\pi a+2\pi d+|M|+1)\). At marker \(B+C(N+1)\) the centre phase exceeds each of these target levels by more than \(M\). The two transverse face inequalities on the seam and the two phase inequalities on the marker endpoints give a rectangle zero for every level. Since its level window determines the index uniquely, the resulting \(N\) markers are distinct. All lie between \(B\) and \(B+C(N+1)\). [Physical counting theorem](../../SolitonClassification/PhysicalMarkerCounts.lean)
