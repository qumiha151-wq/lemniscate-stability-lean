# Quadratically many ordinary double points on genuine rotating closed expanders

For **every sufficiently large integer $n$**, there is a smooth noncircular closed planar free-elastic expander with nonzero rotation, primitive turning number $n$ and centre winding number $n$, whose primitive image has at least
\[
                 (n+1)\Big\lfloor\frac{n+1}{200}\Big\rfloor
\]
**distinct ordinary transverse double points**. In this statement each double point has exactly two preimages during the least geometric period. Both tangent lines exist and they are different. All counted points lie in a single outer annulus.

More generally write $h$ for the signed tangent turning in revolutions over the least support period along the [analytic branch](../IntegerRotatingWinding.md) through the winding-one expander. For every nearby rational $h=m/d$ in lowest terms there are at least $d\lfloor d/200\rfloor$ such double points. The primitive curve consists of $d$ rotated copies of one support traversal. The constants and the least-period assertions refer to the actual orbit, including at rational values with arbitrarily large denominator.

## The verified outer annulus

In the support variables used by the [whole-period enclosure](WholeOrbitFourier.md), $p=X\cdot N$, $q=X\cdot T$, $r=|X|$ and $(r^2/2)_s=q$. The level used here is $r^2=101/2$. The [interval check](caps.py) establishes the following facts about the base orbit.

* On the portion $r^2\ge101/2$ there is exactly one critical point of the radius. It is a nondegenerate maximum, in cell 49217 of the grid with 65536 labels.
* The whole portion lies at normalized parameter between $48950/65536$ and $49500/65536$, in the interior of one traversal. Throughout it $p>11/2$ and $r^2<52$.
* The entire parameter interval $[49030/65536,49420/65536]$ has $r^2>101/2$.

For each grid cell the verifier adds $61/65536$ to the error radius of $r$ using unit speed. For $p$ it uses the component speed bound 90. It compares the resulting cells against every possible zero of $q$ certified in the earlier whole-orbit check. Both crossings of the cut level are transverse. The angular shooting branch, in the normalized parameter of one support period, depends smoothly on pitch. Compactness away from the maximum, the nonzero second derivative there, transversality at the two ends, and the strict enclosure margins preserve all three statements for nearby branches, with $p>5$ in the second. The one-block length stays between 60 and 61. Although the endpoints of a block can have different positions, their radii agree and the annulus stays away from the cut.

## Counting crossings without extra preimages

Use a continuous polar angle $\psi$ on the outer cap. Since $X=qT+pN$, its derivative is $\psi_s=-p/r^2<0$ throughout. Each intermediate radius between the cut and the maximum occurs exactly twice, with one label on each side of the maximum. Label the branches $s_-(r)<s_+(r)$ in arclength. Define their positive angular separation in revolutions by
\[
          H(r)=\frac{\psi(s_-(r))-\psi(s_+(r))}{2\pi}.
\]
As $r$ increases, the first label increases, the second decreases and $\psi_s<0$. Thus $H'(r)<0$ throughout the open radius interval. Its limit at the maximum is zero. At the cut it exceeds $1/200$, since
\[
 \psi(s_-)-\psi(s_+) \ \ge\ \frac5{52}\frac{60\,(49420-49030)}{65536}
                      \ >\ \frac{2\pi}{200}.
\]
The total polar angle change on the cap is also less than $\pi/2$, by $|\psi_s|\le1/r$ and cap length at most $61\cdot550/65536$.

For every positive integer $j\le\lfloor d/200\rfloor$ there is a unique intermediate radius with $H(r)=j/d$. On that circle, the $d$ rotated copies of the first branch meet the $d$ rotated copies of the second in precisely $d$ points. Indeed rotation by $2\pi m/d$ generates all $d$ equally spaced angles, and the two sets of angles differ by $2\pi j/d$. Each branch has only one base label at that radius, and distinct rotations of a nonzero point are distinct. Consequently every resulting image point has exactly two labels, with no possible visit from any other part of the curve. The two polar graphs are transverse since their angular derivatives with respect to radius differ by $2\pi H'(r)\ne0$. Different values of $j$ give different radii, completing the count.

Finally take $d=n+1$ and $m=1-d$. These integers are coprime. The established nonzero derivative of $h$ at $-1$ guarantees that each such rational is realized for sufficiently large $n$. Reversal of orientation changes the two signed winding numbers to $n$ and preserves ordinary crossings. The $d$ blocks are the least geometric period by the previously validated local classification. The one-block length and energy tend to strictly positive finite limits. Thus on this family the lower bound also grows proportionally to the scale-invariant product of bending energy and length.

The outer-cap enclosure uses exact Fourier residuals and interval tests on the true base orbit. Analytic continuation, primitive holonomy, and the double-point count use the written arguments and numerical certificates indicated above. This result supplies a family within the classification problem; an exhaustive list of closed self-similar solutions is still missing.

In two disjoint radial bands the exact crossing count follows from their angular apertures. The fraction of squared covering degree tends to 0.1535760618 in these bands. [Two-band counting formula and checked limit](TwoAnnuli.md)
