# Twelve reflected pure expanders have rotation-free neighborhoods

Normalize the dilation coefficient to one. For each of the twelve previously certified reflected centre-crossing expanders there is an open tube around its support orbit and an open interval of pitches containing zero such that **every periodic support orbit in that tube and pitch interval has pitch zero**. The conclusion applies to closed plane curves of every turning number and allows arbitrary periods and covers. The tube condition concerns the complete support orbit. Orbits can leave the tube and return. The argument supplies no uniform tube for the infinite family at arbitrarily large centre slope.

Existing calculations establish a genuinely rotating family near positive pitch, including rational angular holonomies dense in a small interval. A later continuation located additional integer-angle candidates numerically. An abstract even/odd shooting criterion proves that bifurcation requires a singular odd derivative. The following interval calculations verify the contrary alternative on twelve actual pure solutions, and a transverse multiplier calculation removes the period restriction. [Existing rotating classification](../../RotatingCertificate/LocalClassification/LocalClassification.md) · [Existing pure roots](../ReflectedExpanders/ReflectedExpanders.md)

## A quarter-period test of a full nonsymmetric perturbation

Adjoin the constant pitch $\omega$ as a fifth state coordinate. In the order $(k,v,p,q,\omega)$ the vector field is

\[
(v,-k^3/2-p-\omega q,-kq,1+kp,0).
\]

Two linear reversing involutions are $S=\operatorname{diag}(-1,1,-1,-1,1)$ and $R=\operatorname{diag}(1,-1,1,-1,-1)$. Both negate the vector field after conjugation. Their product $C=RS$ commutes with the flow. At a certified pure root the initial state is $(0,b,0,0,0)$ on the fixed plane of $S$. At quarter period $l$ it reaches the fixed plane of $R$, where $v=q=0$. Write $M$ for the true time-$l$ derivative in the five augmented initial coordinates.

The second quarter transfer is $D=R M^{-1}R$ by reversibility at the seam. The next two quarter transfers are $CMC$ and $CDC$. Hence the full time-$4l$ derivative **based at the seam** is $M(CDC)(CMC)D=(MSM^{-1}R)^2$. Put $J=MSM^{-1}$. The seam acceleration is $A=-k^3/2-p$. When $A\ne0$, the surface $v=0$ is a phase section for every sufficiently close orbit. Reflection takes pitch to its negative and preserves this phase section. A vector odd under $R$ with zero $v$ component has the form $y=(0,0,0,u,w)$.

Suppose $(JR)^2 y=y$. Since $J^2=R^2=I$ and $Ry=-y$, this equation implies $R J y=-J y$. In particular both $y$ and $Jy$ have vanishing projections to $(k,p)$. Write $x=M^{-1}y$. Adding these two projected equations gives

\[
\begin{pmatrix}k_{v_0}&k_\omega\\p_{v_0}&p_\omega\end{pmatrix}
\binom{x_{v}}{x_\omega}=0.
\]

Here each entry is an actual derivative of a terminal coordinate at fixed quarter time. Denote the determinant of this matrix by $D_1$. If $D_1\ne0$ then $x_v=x_\omega=0$. Time translation gives $M(be_k+e_q)=(0,A,0,1+kp,0)$. Substitution in the remaining $(k,p)$ equations yields

\[
\begin{pmatrix}k_{k_0}&k_{p_0}\\p_{k_0}&p_{p_0}\end{pmatrix}
\binom{x_k-bx_q}{x_p}=0 .
\]

Write $D_0$ for this determinant. When $D_0\ne0$, one obtains $x_p=0$ and $x_k=b x_q$. The zero $v$ component of $y$ now gives $A x_q=0$. Thus $x=y=0$. This proves injectivity of the two odd full-return columns, including perturbations that move the curve off its centre crossing. The reversible-return linear algebra is verified in Lean in [QuarterOddRigidity.lean](../../SolitonClassification/QuarterOddRigidity.lean).

For the nonlinear step use coordinates $(k_0,p_0,L;q_0,\omega)$ on the $v=0$ seam section and its variable return time. If the support returns to its initial state at time $L$, reversing about the initial time gives another periodic zero at the same even coordinates and opposite odd coordinates. The injective odd derivative has a two-row left inverse. Projecting onto these rows and applying the implicit function theorem gives local uniqueness of the odd coordinates. Comparing the two zeros forces $q_0=\omega=0$. This argument requires no even rank assumption. In particular it applies to periods near the marked value $4l$. [Odd local rigidity](../../SolitonClassification/OddLocalRigidity.lean)

## Arbitrary periods inside one tube

Restrict $M,S,R$ to the four-dimensional tangent space at fixed pitch. In that space $S=-I+2e_v e_v^\top$. The half transfer after identifying opposite seams is $H=MSM^{-1}R$. Reversibility gives $RHR=H^{-1}$, while $\det H=-1$. The characteristic polynomial is anti-reciprocal of degree four. It factors as

\[
(\lambda^2-1)(\lambda^2-\sigma\lambda+1),\qquad \sigma=\operatorname{tr}H .
\]

The sign and the middle coefficient follow by pairing reciprocal eigenvalues or comparing polynomial coefficients, using the constant coefficient $-1$. The full four-state return is $H^2$. At every root the interval proof gives $|\sigma|>2$. There are two distinct reciprocal transverse multipliers of absolute value different from one and two neutral time-return multipliers at one. The section return removes the flow direction, leaving one simple neutral multiplier. Adding the invariant pitch gives a four-dimensional section map with a two-dimensional generalized eigenspace at one and two hyperbolic directions.

Use a small transverse disk through the marked seam and the Poincaré map following the flow for a time near $4l$. The nonstationary primitive support orbit is an embedded circle by ODE uniqueness. A smooth phase coordinate on a sufficiently small tubular neighborhood restricts to increasing arclength modulo its primitive period on that circle. Its derivative along the support flow is strictly positive there and hence throughout a smaller tube, uniformly for pitch in a sufficiently small interval. Each complete periodic orbit contained in the tube therefore crosses a disk once per phase revolution. The disk can be taken in the `v=0` section near the marked seam, or moved there by a smooth flow shift. Compactness of the base circle and continuity of finite-time flow let us take the tube so small that all such crossings stay in the chosen disk. If $4l$ covers the primitive orbit $m$ times, the marked map is the $m$-th iterate of the first-return map. A periodic sequence of section crossings remains periodic under this iterate and all its points remain in the selected disk.

Choose the particular local centre manifold supplied by Theorem 7(i) of Deng. Its construction intersects a local centre-stable graph capturing forward-confined orbits and a local centre-unstable graph capturing backward-confined orbits. Their intersection contains every complete orbit whose positive and negative iterates remain inside the specified neighborhood. The proof uses the existence of this graph with the confinement property and imposes no uniqueness requirement on centre manifolds. The section map is a smooth local diffeomorphism, as required. [Bo Deng, *Uniqueness of Center Manifold Dynamics*, Theorem 7(i), pp. 6–7](https://www.math.unl.edu/~bdeng1/Papers/DengCenterManifold_20.pdf)

The differential of pitch is nonzero on the whole augmented section and is a left eigenvector of its return derivative at eigenvalue one. It annihilates the stable and unstable generalized eigenspaces, since the derivative minus the identity is invertible on each of them. Its restriction to the two-dimensional centre generalized eigenspace is therefore nonzero. By the submersion theorem, choose a rectangle of centre-manifold coordinates $(a,\omega)$. On a smaller rectangle mapping into this chart the centre return has the form $(a,\omega)\mapsto(g(a,\omega),\omega)$. Both centre multipliers equal one, so its triangular derivative has $g_a=1$ at the base point. Confine the section iterates to a still smaller rectangle on which $g_a>0$. At fixed pitch each coordinate slice is an interval and the map is strictly increasing on its full domain interval. If a periodic point in that interval moved to a larger or smaller coordinate, successive iterates would be strictly monotone until returning to the initial coordinate, a contradiction. Every periodic orbit confined to the tube thus has a fixed point of the marked return, where the odd-rank argument gives zero pitch. This conclusion allows arbitrary geometric winding and covers; it concerns containment of the entire support trajectory.

## Validated inputs and reproduction

[validate_quarter.py](validate_quarter.py) takes the dyadic centre, radius, precision, step count and Taylor order from each existing certified root box. It uses Arb balls on the complete box, including variations in duration and in initial slope. For each base coordinate column and the pitch column write the derivatives as $(a,d,u,v_*)$. Along the pure base equation they obey

\[
(a',d',u',v_*')=(d,-3k^2a/2-u-q\,\delta_\omega,-qa-kv_*,pa+ku).
\]

The pitch derivative has zero initial state and $\delta_\omega=1$. The three other columns are the indicated initial-coordinate vectors and have $\delta_\omega=0$. Before each step the program verifies a Picard enclosure by requiring the integral of the interval field bound to lie strictly inside each tube radius. Finite Taylor polynomials at the current state supply coefficients through order $j-1$. The order-$j$ coefficient on the whole tube bounds the Taylor remainder. No step discards the previous endpoint enclosure. The divergence of the four-state support field is zero, so Liouville's formula gives $\det M_4=1$. The inverse row used in the trace calculation is therefore exactly a row of cofactors. The fourth column is recovered from the time-translation equation at the true root. Finally $\sigma=2e_v^\top M_4^{-1}R M_4 e_v$ because $\operatorname{tr}R=0$.

Table entries are rounded locators. The linked records are outward enclosures over the actual root boxes.

| Centre slope | Seam acceleration | \(D_0\) | \(D_1\) | Half-transfer trace | Interval record |
|---:|---:|---:|---:|---:|---|
| 0.201416 | 20.728659 | 1.141103 | 10.475737 | 523.610416 | [certificate](seventh_odd_rank.json) |
| 0.360873 | -12.006933 | -1.066518 | -5.150260 | 174.299741 | [certificate](third_odd_rank.json) |
| 0.719267 | 4.960649 | 0.929607 | 2.578881 | 32.050902 | [certificate](first_odd_rank.json) |
| 0.775123 | -0.510256 | -1.705052 | -7.631557 | -197.764840 | [certificate](fifth_odd_rank.json) |
| 1.186065 | -4.744085 | 3.722365 | 17.008992 | 450.646104 | [certificate](sixth_odd_rank.json) |
| 2.741838 | -0.450644 | -0.415759 | -0.728941 | -7.384733 | [certificate](second_odd_rank.json) |
| 3.779003 | -1.629399 | -0.943395 | -0.960974 | 18.621217 | [certificate](fourth_odd_rank.json) |
| 4.777115 | 1.427904 | 0.329737 | 1.126794 | -9.965211 | [certificate](eighth_odd_rank.json) |
| 5.722978 | 2.229068 | 0.624998 | 1.141188 | 20.146899 | [certificate](ninth_odd_rank.json) |
| 6.715810 | -2.053015 | -0.281571 | -1.378684 | -11.292321 | [certificate](tenth_odd_rank.json) |
| 7.609790 | -2.701370 | -0.488595 | -1.349589 | 21.202338 | [certificate](eleventh_odd_rank.json) |
| 8.615878 | 2.535950 | 0.249187 | 1.578606 | -12.293057 | [certificate](twelfth_odd_rank.json) |

### Reproduction

Run the following commands in this directory with Python and python-flint 0.9.0. The first command recomputes the twelve complete interval records and compares them with their archived values. The default base input is the previously published [aggregate of twelve root certificates](../ReflectedExpanders/certificates.json). Use `--base-cases PATH` to specify another location of that same input. Each output records the canonical SHA-256 of the case used.

```text
python validate_quarter.py
python check_input_boxes.py
```

The second command uses exact rational arithmetic to check all 216 printed enclosure entries against the input boxes in [QuarterRankIntervals.lean](../../SolitonClassification/QuarterRankIntervals.lean). That Lean module independently evaluates both determinant signs and the trace separation from the interval \([-2,2]\) on all twelve full rational boxes. [QuarterOddRigidity.lean](../../SolitonClassification/QuarterOddRigidity.lean) proves that the two nonzero minors imply injectivity of the odd return derivative. The interval ODE evolution and the subsequent nonlinear centre-manifold argument are computer-assisted mathematical proofs; the two Lean modules check the finite interval arithmetic and linear algebra.

