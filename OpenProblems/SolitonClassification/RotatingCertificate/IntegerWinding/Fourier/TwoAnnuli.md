# How many ordinary double points occur in two radial bands?

Take the [rotating branch](../IntegerRotatingWinding.md) with rational turning per primitive support period \(h=m/d\) in lowest terms near \(h_0=-1\). In the open set
\[
             |X|^2 < 3/40 \quad\text{or}\quad |X|^2>101/2
\]
all self-intersections of the primitive curve are ordinary transverse double points. Let \(H_i(h),H_o(h)\) be the angular apertures defined below, in revolutions. The **exact number** in these two bands is
\[
 N(h)=d\{\lceil d H_i(h)\rceil-1+\lceil d H_o(h)\rceil-1\}.
\]
In particular, along every sequence of distinct reduced rationals tending to \(-1\), \(N(h)/d^2\) converges to a constant between \(0.1535760617\) and \(0.1535760619\). These counts include only the two specified bands. Elsewhere the curve can also intersect itself.

## A single radial minimum inside the lower cut

For the base orbit, \(r=|X|\) satisfies \(r>0.17\) throughout. In the region \(r^2\le3/40\) it has exactly one critical point. It is a nondegenerate minimum in cell 49 of the 65536-cell grid. Throughout this region \(p=X\cdot N>0.005\). The outer band's sole nondegenerate maximum and positive \(p\) were established in the [outer-cap proof](RotatingDoublePointFamilies.md). Use signed phase in revolutions centred at the initial section, so both bands lie away from the ends of the traversal.

The [interval checks](annuli.py) enclose \(r\) from each left grid value using unit speed and the physical cell length \(61/65536\). For every cell which could intersect the lower band they verify \(|k|<9\) and \(r<0.29\). Thus \(|p_s|=|kq|<9(0.29)\), giving a strict positive lower bound for \(p\) throughout each such cell. The grid contains exactly one of the [certified zeros](WholeOrbitFourier.md) of \(q=(r^2/2)_s\) among these cells. The signs at its ends and the two separated, transverse crossings of the cut establish the claim. Nondegeneracy, compactness and continuity in the branch parameter preserve this picture near \(h_0\).

## Angular apertures and their limiting values

On either cap use the continuous lift \(\psi=\theta+\pi/2-\arctan(q/p)\), where \(\theta\) is the tangent angle. It satisfies \(\psi_s=-p/r^2<0\). The aperture \(H_i\) or \(H_o\) is the decrease of \(\psi\) from the first cut point to the second, divided by \(2\pi\). At each radius strictly between the cut and the radial extremum there are exactly two labels in the block. As the radius moves from the extremum to the cut, the two labels separate in opposite directions. Their difference of polar angles in turns increases strictly from zero to the aperture, with nonvanishing derivative in the open interval. Both apertures vary continuously with \(h\), by the transverse cut and analytic dependence of the orbit.

For the base orbit the checker bisects each of the four true cut points using interval signs and evaluates the antiderivative of the Fourier polynomial for \(k\) at the midpoint of each resulting interval. The physical length is \(2\pi\lambda_*\); in signed phase \(\xi\in[-\pi,\pi]\) the angle integral has derivative \(\lambda_* k\). The coordinate error below \(10^{-19}\), \(\lambda_*<10\), and \(|\pi\hat\lambda-\pi\lambda_*|<2\cdot10^{-30}\) give angle integration error below \(10^{-16}\) after fixing \(\theta(0)=0\). The remaining cut-point uncertainty uses \(|d\psi/dt|\le61/0.17<360\) for phase \(t\) in revolutions. The resulting enclosures are
\[
 |H_i(-1)-0.1454958365|<3\cdot10^{-11},\qquad
 |H_o(-1)-0.00808022533|<10^{-11}.
\]
The sum is checked directly. The proof uses the same whole-period transfer to the actual orbit as the curvature and [double-point count](DoublePoints.md).

## Exact count on the primitive closed curve

The whole primitive curve visits \(d\) rotational copies of each cap. On an intermediate circle the \(d\) images on each arm are distinct and equally spaced. The two sets coincide exactly when the angular difference belongs to \((1/d)\mathbb Z\). Each positive integer strictly below \(dH\) gives one such circle, with exactly \(d\) points, and every crossing in the open band arises this way. At each point the two preimages have different tangent lines because the derivative of the angular difference with respect to radius is nonzero. At the extreme radius there is just one label per block and the \(d\) image points are distinct. The cut itself is excluded, accounting for the strict inequality when \(dH\) is an integer.

Thus each cap contributes \(d(\lceil dH\rceil-1)\). As \(h=m/d\) tends to \(-1\) through distinct reduced rationals, \(d\to\infty\), so dividing by \(d^2\) gives the stated limit. At \(h=(1-d)/d\), reversing orientation gives every sufficiently large positive turning number \(n=d-1\), also the winding about the centre. For these curves the number of distinct ordinary crossings in the bands alone is at least
\[
 (n+1)\left(\left\lfloor 145(n+1)/1000\right\rfloor+
                 \left\lfloor 8(n+1)/1000\right\rfloor\right).
\]
These results use the written holonomy and analytic branch arguments and the interval data. An end-to-end Lean verification of this family is still outstanding.

Over the whole primitive curve the number of distinct ordinary transverse double points has a quadratic asymptotic with coefficient strictly between 10.09 and 14. [Global counting theorem](OrdinaryCrossingAsymptotic.md)
