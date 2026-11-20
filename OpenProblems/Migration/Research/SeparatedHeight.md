# A perimeter bound for a separated expansion centre

Let \(X:\mathbb R/L\mathbb Z\to\mathbb R^2\) be a smooth closed unit-speed immersion. Write \(T=X_s,\ N=JT,\ p=X\cdot N\). Suppose the origin satisfies the normal-distance balance
\[
                       \int_0^L p N\,ds=0.                         \tag{1}
\]
This holds for the actual expansion centre of every pure homothetic free-elastic-flow profile, since \(W=(k^2/2)T+k_sN\) satisfies \(W_s=(k_{ss}+k^3/2)N=-a pN\) with \(a>0\). It also holds for the centre minimizing the integral of squared normal distances of any closed regular curve.

**Theorem.** For every unit \(e\) such that the actual height \(h=X\cdot e\) is strictly positive throughout the curve,
\[
 \left(\int_0^L h^{-2}\,ds\right)
 \left(\int_0^L h_s^2\,ds\right)>64 .                            \tag{2}
\]
Consequently \(\min h<L/8\). In particular, if a pure homothetic profile has its centre outside its convex hull, the distance from the centre to that hull is strictly less than one eighth of the profile perimeter. The statement applies to every turning number and every bending energy.

**Proof.** Set \(y=X\cdot Je\). In the oriented frame \((e,Je)\), the normal is \((-y_s,h_s)\) and \(p=-hy_s+yh_s\). Testing (1) in both coordinate directions, and taking a linear combination, gives for every real \(\lambda\)
\[
 \int (hy_s-yh_s)(y_s-\lambda h_s)\,ds=0 .
\]
Write \(f=y-\lambda h\). The equality becomes \(\int h f_s^2=\int h_s f f_s\). Completing the square with \(u=f/\sqrt h\) gives the exact identity
\[
                    4\int h^2 u_s^2\,ds=\int h_s^2u^2\,ds.        \tag{3}
\]
Choose \(\lambda\) so that \(\max u+\min u=0\). Indeed \(u=y/\sqrt h-\lambda\sqrt h\); on the compact parameter circle \(\sqrt h\) has a positive minimum, and the sum of the two extrema varies continuously from positive to negative values. Write \(\max u=-\min u=M\). If \(M=0\), then \(y=\lambda h\) on the entire curve. No regular closed immersion can be contained in a line, so \(M>0\).

The two arcs between a maximum and a minimum each contribute at least \(2M\) to the total variation. By Cauchy–Schwarz and (3),
\[
 16M^2\le\left(\int|u_s|\right)^2
 \le\left(\int h^{-2}\right)\left(\int h^2u_s^2\right)
 \le\frac{M^2}{4}\left(\int h^{-2}\right)\left(\int h_s^2\right).
\]
The Cauchy–Schwarz inequality here is strict. Equality would imply \(|u_s|=C h^{-2}\) everywhere by continuity. At an extremum of \(u\) its derivative vanishes, forcing \(C=0\), contrary to \(M>0\). This proves (2). If \(d=\min h>0\), then \(\int h^{-2}\le L/d^2\) and \(\int h_s^2\le L\). Thus \(d<L/8\). For a centre outside the compact convex hull, take \(e\) along its closest-point projection onto that hull; then \(d\) is exactly the distance in question.

**Required dilation and elapsed time.** Let two slices of the same expanding homothety lie on opposite strict sides of one line. Use the earlier slice for \(X\) and orient \(e\) so the later slice is on the side of higher \(e\)-coordinate. With the centre as origin, the later slice is \(\rho X\), \(\rho>1\). Put \(d=\min X\cdot e\) and \(W=\max X\cdot e-d\). Strict separation implies \(\rho d>d+W\), hence \(d>0\) and
\[
                 \rho>1+\frac Wd>1+\frac{8W}{L}.                  \tag{4}
\]
Writing \(E=\tfrac12\int k^2ds\) and \(a\) for the dilation coefficient at the earlier slice, \(\rho^4=1+4a\,\Delta t\). The periodic identities \(\int kF=aL\), \(\int F^2=aE\) give \(a\le 2E^2/L^2\) by Cauchy–Schwarz. Therefore a strict two-slice separation requires
\[
             \Delta t>\frac{L^2}{8E^2}
                 \left[\left(1+\frac{8W}{L}\right)^4-1\right].
\]
These restrictions leave open profiles with arbitrarily small positive support height relative to their perimeter. They give no universal centre-in-hull theorem for such profiles.

## The centre of a rotating expander from the position and tangent

Let \(O\) be the actual similarity centre and \(a>0,\ \omega\in\mathbb R\) the instantaneous dilation and angular coefficients. Use \(N=JT\), where \(J\) is positive quarter rotation. The equation in this convention is
\[
 F=-a(X-O)\cdot N-\omega(X-O)\cdot T .
\]
The two points \(C_N,C_T\) minimizing \(\int((X-c)\cdot N)^2\) and \(\int((X-c)\cdot T)^2\), respectively, depend only on the given closed curve. Both minimizers are unique. The two Gram matrices \(G_N=\int NN^\top,\ G_T=\int TT^\top\) are positive definite, since the tangent of a regular closed immersion cannot be confined to one unoriented line. They obey \(G_N J=J G_T\).

The actual centre and angular ratio satisfy
\[
 a(C_N-O)+\omega J(C_T-O)=0,\qquad
 O=(aI+\omega J)^{-1}(a C_N+\omega J C_T).                    \tag{5}
\]
Indeed \(\int F N=0\) by the stress balance, and the normal equations of the two minimizations reduce this identity to \(aG_N(C_N-O)+\omega JG_T(C_T-O)=0\). Substituting \(JG_T=G_NJ\) factors the left side as \(G_N[a(C_N-O)+\omega J(C_T-O)]\). Multiplication by \(G_N^{-1}\) proves (5). In particular \(O\) belongs to the circle with diameter \(C_NC_T\), allowing a point circle, and
\[
 |O-C_N|=\frac{|\omega|}{\sqrt{a^2+\omega^2}}|C_T-C_N| .
\]

For a nonround curve the angular ratio in (5) can itself be recovered from first-order geometry. Define \(p_0=(X-C_N)\cdot N,\ q_0=(X-C_T)\cdot T\). Then
\[
 \frac{\omega}{a}=-\frac{\int p_0q_0}{\int q_0^2}.             \tag{6}
\]
To see this, (5) gives \(F=-a p_0-\omega q_0\) pointwise. Rotation about \(C_T\) gives
\(\int Fq_0=\int W_s\cdot J(X-C_T)=-\int W\cdot N=-\int k_s=0\).
Finally \(q_0=\frac12(|X-C_T|^2)_s\). Vanishing of its square integral forces constant radius and hence a round immersed circle, possibly multiply covered. This proves (6) whenever the curve is nonround.

In particular, any nonround profile having a reflection symmetry as an arclength immersion has \(\omega=0\). Both minimizing centres transform equivariantly under rigid motions. Under a reflection with linear part \(R\), accompanied by an arclength change \(s\mapsto \sigma s+s_0,\ \sigma=\pm1\), the tangent transforms as \(\sigma RT\) and the normal as \(-\sigma RN\). Consequently the mixed integral \(\int p_0q_0\) changes sign and is invariant under reparametrization. It vanishes on a reflection-symmetric curve.

The absolute rate follows by adding the bending energy. For \(t=\omega/a\) and \(z=p_0+t q_0\), both normal equations give \(\int zN=0\), and (6) gives \(\int zq_0=0\). Thus the dilation virial \(\int F(X-O)\cdot N=-E\) reduces to \(a\int z^2=E\). The denominator is positive because a regular closed curve has positive bending energy.

Equations (5) and (6) recover the centre of any nonround similarity profile from its parametrized image and first derivative. Applying the perimeter estimate to \(C_N\) gives \( \operatorname{dist}(C_N,\operatorname{conv}X)<L/8\) whether this centre is outside or inside. Consequently
\[
 \operatorname{dist}(O,\operatorname{conv}X)
 <\frac L8+\frac{|\omega|}{\sqrt{a^2+\omega^2}}\,|C_T-C_N|.
\]
The centre-in-hull test with (5) is equivalent to the absence of strict two-slice separation anywhere along the entire forward self-similar motion. If \(O\) belongs to the initial convex hull, all later convex hulls contain it. Otherwise strict separation of \(O\) and the initial compact hull puts the whole initial curve at positive height relative to \(O\). A pure expansion eventually has minimum height larger than the earlier maximum. For \(\omega\ne0\) the rotation angle is \((\omega/a)\log\rho\) at dilation factor \(\rho\). At its first half-turn the later curve has strictly negative height in the same direction. This equivalence provides a criterion on a candidate shape. It leaves open whether an actual closed elastic expander passes the exterior-centre test.

## Verification scope

The independent Migration project proves the strict weighted inequality (2), its directional one-eighth consequence, the two-slice dilation bound, and the elapsed-time bound under the fourth-power evolution law. The nearest-point passage to convex-hull distance and the rotating-centre formulae (5) and (6) are proved in this note. The module and full-project audit record the precise Lean hypotheses and the checked declarations. [Lean module](../Migration/SeparatedHeight.lean) · [Local verification record](SeparatedHeightVerification.json)

The equivalence in the last paragraph now has a Lean proof for actual similarity slices, including their physical times and arbitrary surjective changes of parameter. At every sufficiently large dilation, the initial slice is strictly separated from the later one for every rotation. [Geometric and physical statements](SimilarityMigration.md) | [Integrated verification](SimilarityVerification.json)
