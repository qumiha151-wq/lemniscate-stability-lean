# Entry of centre shots into a fixed radial section

Normalize the dilation coefficient to one and start from physical support data \((k,v,p,q)=(0,b,0,0)\), with \(b>0\). Write \(\delta=1/b\), \(t=\sqrt{\delta}\,s\), and \(\rho=\sqrt{\delta}\,|X(s)|\). The moving section is the incoming equation \(-\operatorname{height}(X)=H\), with height evaluated from all four physical support coordinates.

There are constants \(H_0\ge2\) and \(K>0\) such that for each \(H\ge H_0\), every sufficiently large \(b\) has a crossing at some \(t\in[1,T]\), where \(T\le10000\) is a critical layer time. The incoming height is strictly above \(H\) at \(1\) and strictly below \(H\) at \(T\). At every such crossing in the interval the raw transverse impact satisfies \(|I|\le K/H\). On the entire interval the equation uses regular coordinates, the radial direction cosine is at least \(1/12000000\), and \(\epsilon^3\le1200^4/b^2\) for the inverse radius parameter \(\epsilon=|X|^{-4/3}\).

Let \(r\) be the square root of the outer stress amplitude, \(a,\beta\) the two components of the scaled position in its stress frame, and \(n\) the square root of the physical stress amplitude divided by \(|X|^{1/3}\). Direct substitution in the original support coordinates gives

\[
     n^3\rho\delta=r^3,\qquad I n^2\rho^2\delta=\beta r^3 .
\]

The quartic oscillator coordinates agree in the two frames. The corrected descent bound \(|\beta|r^3\le C\delta\) therefore yields \(|I|n^2\rho^2\le C\). For \(n\ge1\), the height correction has absolute value at most one. Because the elementary radial direction cosine is at most one, \(H\le n^2+1\) at every crossing. The bound \(\rho\ge1/1200\) now gives \(K=2\cdot1200^2 C\).

For the existence of a crossing, fix the critical threshold \(L\) once, above the descent threshold and \(40000\). On the final section \(r^3=L\delta\), so \(n^3\rho=L\) there. This bounds the final height independently of \(b\). At \(t=1\), the outer amplitude is at least \(1/2\). The same scale identity, the upper bound \(\rho\le10000\), and the lower direction-cosine bound force the initial incoming height to exceed any prescribed \(H\) as \(b\) increases. The intermediate value theorem on the regular physical curve supplies the crossing.

For every crossing in this strip, the true lifted oscillator angle satisfies \(\theta(t)\ge b/8\). Indeed the verified initial winding already gives \(\theta(1)\ge b/8\). Subsequently \(n\ge1\) implies \(r^3\ge\rho\delta\), and the magnitude of the position's projection onto the normal is at most \(\rho\). Since the normalized oscillator satisfies \(|U|\le2\), its forward phase speed is nonnegative throughout this part of the trajectory. The oscillator amplitude stays positive on the whole interval from the centre. [Angle estimate and trigonometric identities](../../SolitonClassification/PhysicalIncomingWinding.lean)

The geometric conversions, the finite-interval crossing argument, and their application to arbitrary sufficiently large centre slopes are separate Lean statements. [Coordinate identities](../../SolitonClassification/OuterIncomingCoordinates.lean) · [Section estimates](../../SolitonClassification/OuterIncomingSection.lean) · [Physical centre shots](../../SolitonClassification/PhysicalIncomingCrossing.lean)
