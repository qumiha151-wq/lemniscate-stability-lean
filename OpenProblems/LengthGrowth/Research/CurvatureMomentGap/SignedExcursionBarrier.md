# Two opposite curvature excursions on any putative super-quarter-power flow

Fix a smooth closed planar free elastic flow and its signed turning integral \(S=\int k\,ds\). Write \(L\) for length, \(E=\tfrac12\int k^2ds\), \(U=EL\) and \(m=\sqrt{2E/L}\). A record at time \(t\) means \(U(t)\ge U(s)\) for every \(0\le s\le t\).

**If the fourth-root length bound fails**, then for every
\[
       0\le d<(\sqrt{17}-1)/4=0.7807764\ldots
\]
there are arbitrarily late records with arbitrarily large \(U\) at which *both* \(\min k<-dm\) and \(\max k>dm\). The two excursions occur on the very same curve at the very same record. Equivalently as a sufficient condition, suppose there exist \(d\) in this interval and finite thresholds in time and product such that on each record beyond both thresholds at least one of the two strict excursions is absent. Then \(L(t)=O((1+t)^{1/4})\) for this initial curve. The missing side may change with time. Both assertions are verified for the actual geometric flow in [HighRecordExcursions.lean](../../LengthGrowth/ActualFlow/HighRecordExcursions.lean).

The bound at each individual slice keeps the turning information. Take either signed normalization \(r=m\) or \(r=-m\), and put \(K=k/r\), \(\mu=\langle K\rangle=S/(Lr)\), \(H=\langle K^3\rangle\), with arclength averages. At any positive time with \(U'\ge0\), if \(K\ge-d\) everywhere and \(\mu<1\), then
\[
                         2+\mu\le 2(1+\mu)d^2+d.
\]
This conclusion follows from the force of the actual flow. Define \(v=F/r^3\), where \(F=k_{ss}+k^3/2\). Then \(\langle v\rangle=H/2\), \(\langle K^2\rangle=1\), and
\[
 {U'\over L^2r^6}
 =\tfrac12\langle Kv\rangle-\langle v^2\rangle
 =\tfrac1{16}-\langle(v-K/4)^2\rangle .
\]
Taking the mean inside the square gives \((2H-\mu)^2\le1\). On the other hand, for all \(x\in\mathbb R\),
\[
 0\le\langle(K+d)(K-x)^2\rangle
     =(\mu+d)x^2-2(1+d\mu)x+H+d.
\]
The discriminant inequality and \(\mu+d\ge0\) imply \((1+d\mu)^2\le(\mu+d)(H+d)\le(\mu+d)((1+\mu)/2+d)\). Subtraction and cancellation of \(1-\mu>0\) give the claim. On high records of a fixed flow, \(|\mu|=|S|/\sqrt{2U}\) tends to zero. This yields the displayed universal constant and the actual counterexample test. [Moment inequality](../../LengthGrowth/ActualFlow/CurvatureMomentCone.lean) · [Physical curvature and force](../../LengthGrowth/ActualFlow/PhysicalCurvatureExcursion.lean)

For perspective, the limiting algebraic constraint \(2d^2+d\ge2\) is saturated in the abstract two-point moment problem: take \(K=-d,1/d\) with probabilities \(1/(1+d^2),d^2/(1+d^2)\), respectively. The mean is zero, its second moment is one, and its third moment is \(1/d-d=1/2\) at the limiting \(d\). This auxiliary distribution is not a smooth curvature profile. In fact the independent [strict cubic gap](StrictHalfThreshold.md) gives a stronger written asymptotic obstruction: if \(\epsilon>0\) is its universal gap, replace \((\sqrt{17}-1)/4\) in the counterexample test by the positive solution of \(d^2+(1/2-\epsilon)d=1\). Indeed, along high increasing records \(|H|\le1/2-\epsilon\), so the preceding discriminant inequality passes to \(1\le d(d+1/2-\epsilon)\) on any sequence where one excursion is missing. This last strengthening is a written deduction. The universal existence of a length bound, or of one trajectory violating it, remains open.
