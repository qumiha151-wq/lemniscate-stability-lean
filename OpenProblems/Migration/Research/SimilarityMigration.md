# Detecting migration of an actual self-similar planar curve

Let \(K\subset\mathbb C\) be the compact image of the initial closed
curve, let \(O\) be its similarity centre, and let \(H=\operatorname{conv}K\).
For a global smooth closed free elastic flow whose positive-time images
are direct similarities of \(K\) about the same \(O\), the centre criterion
is complete within this class. If \(O\notin H\), from **every prescribed
earlier slice** one can find a strictly separated slice arbitrarily late.
If \(O\in H\), no two slices are strictly separated. The actual-flow
theorem assumes only the similarity of the images about \(O\); it
deduces the existence of large multipliers from the evolution equation,
without prescribing rates, rotation or dilation growth.

For an expanding similarity with dilation \(\rho\) and angular ratio \(b\),
the image is \(O+\rho e^{ib\log\rho}(K-O)\).
The following statements are equivalent.

- \(O\notin H\).
- There is a later slice strictly separated from \(K\) by a straight line.
- Two forward slices are strictly separated by a straight line.

Two separated slices can also be found after any prescribed logarithmic
dilation. Each assertion concerns the entire two images. The separating
line has a real offset and a Euclidean unit normal. If \(O\in H\),
every later convex hull contains \(O\). If \(O\notin H\), a strictly
separating functional for \(O\) and \(H\) puts the initial image at a
uniformly positive relative height. A pure dilation eventually lifts the
whole later image above the initial maximum; when \(b\ne0\), a half turn
places the later image on the opposite side of a line through \(O\).
The proof establishes compactness of the ordinary planar convex hull
using Carathéodory's theorem.

For a family of actual closed immersions, the period-image equals the
range over the full real parameter line. A surjective reparametrisation
at each time, including reversal of orientation, therefore preserves
the criterion. With initial dilation one and initial angle zero, the
physical rate equations \(\rho'=a/\rho^3\),
\(\theta'=ab/\rho^4\), \(a>0\), imply
\(\rho^4=1+4at\) and \(\theta=b\log\rho\). The logarithmic elapsed
coordinate is increasing and every nonnegative value has an explicit
physical-time preimage. These facts connect the initial-slice and
two-slice statements to the actual position function.

## A bound uniform in the rotation

Write \(d=\operatorname{dist}(O,H)\). Suppose an earlier image is
contained in the closed disk \(\overline B(O,R)\), and every point of
a later image lies within distance \(\varepsilon\) of some point of
\(O+c(K-O)\), with any complex multiplier \(c\). Then
\[
 R+\varepsilon<|c|d
 \quad\Longrightarrow\quad
 \text{one straight line strictly separates both images.}
\]
Indeed the later image lies in the sum of the transformed initial hull
and the error disk. This sum is compact and convex, and its distance
from \(O\) is at least \(|c|d-\varepsilon\). The earlier disk and this
sum are disjoint compact convex sets, which admit strict linear
separation. In particular if \(d>0\), every sufficiently large scaling
separates the initial and later images, uniformly in the rotation.
The separating line may depend on the later time.

The modules SimilarityHull, SimilarityClock, SimilarityFlow and
EscapingHulls prove these statements. The criterion still requires
locating the actual centre with respect to the actual initial convex
hull. No example of a closed migrating free elastic flow is asserted.

## A bound on the time spent in disks

For a smooth closed free elastic flow, assume that at each time
\(v\in[s,t]\) its entire image fits inside a disk of radius \(R>0\).
The disk centre is allowed to depend arbitrarily on \(v\). Writing
\(E(v)=\frac12\int k^2\,ds\), the module DiskDissipation proves
\[
 t-s\le 2R^5\,[E(s)-E(t)] .
\]
This follows from the length and dilation variations on the actual
curve, a directional width estimate, and energy dissipation. On
arbitrarily late slices of every global smooth closed free elastic
flow, no disk of the prescribed radius can contain the image. The
statement concerns arbitrarily late slices and by itself supplies
no limit for the enclosing radius on all large times.

Together with similarity of the images, escaping every fixed disk
forces arbitrarily large similarity multipliers, since \(K\) is bounded.
The uniform-in-angle separation estimate then applies to any fixed
earlier slice when \(d>0\). This proves the arbitrary-late assertion in
SelfSimilarEscape. Establishing whether a closed elastic flow satisfying
the exterior-centre condition exists remains open.
