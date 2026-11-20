# The verified rotating profiles have a fixed arclength centroid

Every closed profile obtained in the certified dense-pitch construction has its arclength centroid at its fixed centre of similarity. This remains true after any spatial translation, at every time of its rotating and expanding flow. Consequently none of these solutions migrates from an open half-plane into its opposite, and none has a divergent arclength centroid. The migration question for general closed free elastic flows remains open. [Original question, §1.2](https://arxiv.org/html/2404.12619v3#S1.SS2)

## Finite rotations and the arclength centroid

Identify the plane with the complex numbers and take the centre as the origin. Suppose a continuous unit-speed profile $z$ has a block of length $P>0$ with

$$
z(s+P)=wz(s),\qquad w\ne1,\qquad w^d=1,\qquad d\ge2.
$$

Then $L=dP$ is a closing period. Write $I=\int_0^L z(s)\,ds$. Integrating the one-block shift gives $wI=\int_P^{L+P}z(s)\,ds=I$, by periodicity. Thus $I=0$. In physical coordinates a similarity slice has the form $C+A z(s)$, with a fixed centre $C$ and a time-dependent nonzero complex multiplier $A$. Its arclength element is $|A|\,ds$, its length is $|A|L$, and its arclength centroid is exactly $C$. An arclength shift, an integer cover or a tangential reparametrisation gives the same centroid.

The same centre belongs to the ordinary convex hull of each slice. The $d$ points $C+Aw^j z(0)$, $0\le j<d$, occur at $s=jP$. Their average is $C$, since $\sum_{j=0}^{d-1}w^j=0$. Two disjoint convex sets cannot contain two entire slices whose convex hulls share $C$. This applies to the two open half-planes determined by any fixed line. The argument allows the orientation and scale of the two slices to differ.

These implications are proved in the independent Migration project as `mean_eq_zero`, `slice_mean_eq_center`, `center_mem_slice_hull` and `no_separated_slices` in the namespace `MigrationGeometry.FiniteRotation`. They use mathlib's one-period integral identity and finite convex-combination lemma. [Lean source](../Migration/FiniteRotation.lean)

## Why the verified family has this symmetry

Use $p=z\cdot N$, $q=z\cdot T$ and tangent angle $\theta$, measured in coordinates relative to the similarity centre. The actual position reconstructed in SolitonClassification is $z=(q+ip)e^{i\theta}$. Its endpoint matching propagates to all arclengths by the autonomous trajectory law. Over $P=2c_2>0$, both support coordinates repeat and the tangent angle changes by $H=-112\pi/57+t$. Hence $z(s+P)=e^{iH}z(s)$ for every $s$. The closing angle is distinct from the positive pitch $c_4$. [Support-coordinate reconstruction](../../SolitonClassification/SolitonClassification/SupportODE.lean) · [One-block identities used in the closure proof](../../SolitonClassification/SolitonClassification/Rotating/RotatingClosedProfileClosure.lean)

The dense-pitch proof constructs, in each open pitch subinterval of its conclusion, an actual root and a rational $u$ with $H=2\pi u$. Its Lean parameter ball has radius $10^{-24}$, and its angle-offset bound is $|t|\le10^{-24}/200=5\cdot10^{-27}$. The earlier quantitative analysis uses a parameter cube of radius $10^{-32}$ and $|t|\le5\cdot10^{-35}$ to exhibit the explicit pitch interval $(b_0-5\cdot10^{-34},b_0+5\cdot10^{-34})$. These are distinct bounds on distinct constructions. Both angle bounds imply $|t|<2\pi/57$, which suffices here. [Lean branch proof](../../SolitonClassification/PitchLinuxFollowup/sources/SolitonClassification/CandidatePitchBranch.lean) · [Quantitative branch analysis](../../SolitonClassification/Pitch/PitchAccumulation.txt)

Indeed, $-1<u=-56/57+t/(2\pi)<-55/57$. For every reduced rational $u=a/d$ produced this way, $e^{2\pi i u}$ has finite order $d\ge3$. The centre root has $u=-56/57$ and closes after 57 blocks. The geometric arguments above apply without needing to identify the shortest support or geometric period. In fact, choosing any nonzero point of the profile gives a regular $d$-gon in each similarity slice. Its interior contains the centre, so the centre lies in the interior of the slice's convex hull as well.

The passage from each constructed shooting witness to the abstract Migration lemmas is the mathematical argument in this section. The exported dense-pitch theorem states closure and nonconstant curvature. Its proof supplies the offset, rational angle and block recurrence used here. The Migration project can therefore be built independently of the large numerical proof packages. [Verified pitch run](https://github.com/qumiha151-wq/lemniscate-stability-lean/actions/runs/44657378217)
