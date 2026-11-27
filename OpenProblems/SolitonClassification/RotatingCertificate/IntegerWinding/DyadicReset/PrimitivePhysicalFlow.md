# Physical evolution of a winding-minus-one rotating profile

Let $X$ be a smooth closed unit-speed immersion whose tangent angle changes by $-2\pi$ in the stated period $L>0$. Its signed curvature satisfies

$$
k_{ss}+k^3/2=-X\cdot N-bX\cdot T .
$$

The physical time interval is $t>-1/4$. Put $r=(1+4t)^{1/4}$ and $\tau=\log r$. At time $t$ the image is exactly $rR_{b\tau}X(\mathbb R)$, where $R_\alpha$ denotes rotation by $\alpha$. A periodic smooth vector field $bX\cdot N-X\cdot T$ supplies the required time-dependent parametrization. Lean verifies joint smoothness, nonvanishing speed, the length $rL$, and the identity $X_t=-(k_{ss}+k^3/2)N$ for the full coordinate velocity. The proof calculates speed, signed curvature, arclength derivatives, and the unit normal from the evolving coordinates. [Physical evolution](../../../SolitonClassification/Rotating/IntegerPhysicalEvolution.lean)

The computed arc contains the square $[-1/20,1/20]^2$ in its convex hull. Since the material reparametrization is onto, every convex hull of the corresponding closed similarity motion contains the closed Euclidean disk of radius $r/20$ about the same center. [Image and disk](../../../SolitonClassification/Rotating/IntegerPhysicalHull.lean)

The rate $b$ is intrinsic even when a different center and an arbitrary translation are allowed. Subtract two planar similarity generators with the same normal velocity. Along the profile the difference $V$ is tangent. If $a$ is the dilation difference, the tangential component $w=V\cdot T$ satisfies $w'=a$. Periodicity forces $a=0$, so $w$ is constant. Differentiating $V\cdot N=0$ then gives $b_1-b_2=kw$. The curvature takes both signs. Thus $w=0$, the rotation coefficients agree, and both translation components agree. In the chosen coordinates the unique dilation, rotation, and translation parameters are $1,b,0,0$, with $0.10<b<0.11$. [Uniqueness of the generator](../../../SolitonClassification/Rotating/IntegerPhysicalGenerator.lean)

The indexed theorem combines these conclusions with the precise polynomial-cell hypotheses for the two signed arms. [Indexed physical theorem](../../../SolitonClassification/Rotating/IntegerPhysicalFromRows.lean)
