# Rigidity of closed similarity profiles with low bending product

Let \(X\) be a smooth regular closed planar curve whose free elastic flow consists of similarities of \(X\), up to reparametrization. If its length and squared-curvature integral satisfy \(L\int k^2\,ds\le4\pi^2+36\), its image is a circle covered once. This includes similarity motions combining dilation, rotation and translation. The quantity \(U=L\int k^2\,ds\) is unchanged under all those operations. Along the flow it is constant. The strict decrease theorem for noncircular slices therefore forces \(k\) to be constant. The turning estimate in the same proof forces the absolute turning number to be one. A regular closed planar constant-curvature curve with that turning number traces a circle once. Conversely an expanding circle is an exact solution.

## Independent classification theorem

The classification project proves this result from its own planar coordinates and unit-speed Frenet equations. The normal force in the hypothesis is computed from the derivatives of the actual position. The equation permits any translation vector, dilation coefficient and rotation coefficient. A nonzero dilation–rotation pair absorbs the translation by solving for its center. A pure translation, including zero velocity, is ruled out by the project's existing closed-translator theorem.

For the centered equation the periodic support variables are constructed from the position. The two identities \(\int kF=aL\) and \(\int F^2=aB/2\) force equality of the scale-invariant bending rate. The project's own turning-number and fourth-moment estimates give \(LB=4\pi^2\). The centered curvature variance therefore vanishes, and periodicity gives \(k=K\) at every arclength point. The final theorem derives actual complex coordinates
\[
 X(s)=O+A\exp(iKs),\qquad A\ne0,\qquad KL\in\{-2\pi,2\pi\}.
\]
The arclength data, turning estimate, moment argument, and native profile theorem build inside SolitonClassification. [Parametrized classification theorem](../../SolitonClassification/LowBendingCircles.lean) · [Curvature rigidity](../../SolitonClassification/LowBendingProfileRigidity.lean) · [Classification audit](RigidityVerification.json)

The [separate physical-flow length proof](../../../LengthGrowth/Research/BendingSublevel/DefectThirtySix.md) gives monotonicity and fourth-root growth for the same initial sublevel. Classification above the threshold remains open.
