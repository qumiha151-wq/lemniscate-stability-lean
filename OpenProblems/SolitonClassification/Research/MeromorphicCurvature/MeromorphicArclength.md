# Single-valued meromorphic arclength curvature

Let a smooth closed immersed plane curve be a free-elastic similarity profile. Suppose its signed curvature in the actual arclength parameter has a single-valued meromorphic continuation to the entire complex plane. It is a covered circle or a covered Bernoulli lemniscate. The result allows functions of arbitrary growth, arbitrary rotation and translation coefficients, and arbitrarily many poles. The given real curve is regular at all real arclengths.

The machine-checked converse characterizes this class by a real curvature equation. For the periodic support profile, the global meromorphic continuation exists exactly when the curvature is a nonzero constant or satisfies \(k''+2k^3/9=0\). For that second branch the full position is a rotated, translated and scaled copy of \(\sin u/(1+i\cos u)\); it is traversed an integer number of times, the rotation rate vanishes, and the scale \(d\) and dilation coefficient \(a\) satisfy \(a d^4=15/2\). The specific closed rotating profile with two double points has no such global meromorphic continuation.

[Physical classification and analytic converse](../../SolitonClassification/MeromorphicClosedProfile.lean) · [The verified example outside the class](../../SolitonClassification/EllipticRotatingObstruction.lean)

## The two possibilities on the complex plane

The true position and normal-force equations imply the complex identity
\[
 2(kk''''-k'k''')+3k^2(k')^2+5k^3 k''+k^6-2ak^2-2bk'=0 .
\]
It holds on every punctured neighborhood by the meromorphic identity theorem. A closed profile has positive dilation coefficient after centering.

**Without a pole.** Entire solutions of this equation are constant, even for arbitrary complex coefficients \(a,b\) and without a real periodicity assumption. Write \(M(r)=\max_{|z|\le r}|k(z)|\) and \(H(r)=\sqrt{1+M(r)}\). Above every initial radius there is some \(r\) with \(H(r+4/H(r))\le2H(r)\). Otherwise repeated doubling would make the function unbounded on a fixed compact disk. At a point where the maximum on the smaller disk is attained, Cauchy's estimate gives \(|k^{(j)}|\le 4j!H^{j+2}\). On substitution, every term other than \(k^6\) is bounded by \((472+2|a|+8|b|)H^{10}\). But \(|k|^6=(H^2-1)^6\). Thus \(M(r)\) stays bounded and Liouville's theorem applies. [Entire-solution theorem](../../SolitonClassification/EntireCurvatureRigidity.lean)

**At a pole.** The local Laurent calculation gives a simple pole with residue \(c=\pm3i\), and the regular part starts at order three. Reflect about this pole \(x\) and change sign, obtaining another solution \(\widehat k(z)=-k(2x-z)\) with the same residue. If their difference has first nonzero term \(d(z-x)^m\), its regular order \(m\ge0\) must satisfy
\[
 cd(m+2)(m-5)(2m^2-4m-21)=0.
\]
The quadratic factor is an odd integer. Thus \(m=5\). Yet \(k-\widehat k\) is even about the pole, and a nonzero even germ cannot start in degree five. This proves the global identity \(k(2x-z)=-k(z)\). [Indicial calculation](../../SolitonClassification/MeromorphicPoleIndicial.lean) · [Even-germ argument](../../SolitonClassification/MeromorphicPoleParity.lean)

Reality along the real axis implies conjugation symmetry on the whole plane. Combining the odd reflections about \(x\) and \(\bar x\) yields the period \(2(x-\bar x)\). It is nonzero and purely imaginary because the original real curvature is regular. The closed curve supplies the real period. The continuation is therefore elliptic. At every pole the defect \(k''+2k^3/9\) has a removable singularity with value zero. This defect is entire and doubly periodic, hence zero. [Elliptic rigidity and position reconstruction](../EllipticCurvature/EllipticArclength.md)

## Existence on the Bernoulli branch

For the normalized signed curvature \(w\), one has \(w(0)=0,\ w'(0)=1,\ (w')^2+w^4=1\). A local inverse near the origin gives a holomorphic germ. The duplication formulas for \(w,w'\) extend the germ meromorphically to successively doubled disks. The real continuation matches the arclength oscillator, and \(w(iz)=iw(z)\) gives a second period from the real one. Shifts of the real arclength origin and positive spatial rescalings are included. [Continuation proof](BernoulliEllipticContinuation.md) · [Lean construction](../../SolitonClassification/LemniscaticElliptic.lean)

