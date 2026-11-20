# Local classification around a hyperbolic rotating free-elastic expander

Normalise the dilation coefficient to one and the similarity centre to the origin. Use oriented arclength and write the pitch as $b$. In the coordinates $z=(k,u,p,q)$, where $u=k_s/8$, $p=X\cdot N$ and $q=X\cdot T$, the ordinary differential equation for a profile is

\[
z'=(8u,-k^3/16-p/8-bq/8,-kq,1+kp).
\]

Along an orbit set $\theta'=k$ and reconstruct $X=qT+pN$, with $T=(\cos\theta,\sin\theta)$ and $N=JT$. The equations give $X'=T$. The remaining freedom in reconstruction is a rotation and a choice of arclength origin.

Let $b_*$ be the actual root of the certified contracting shooting problem with block angle $-112\pi/57$. The root is near $0.0096866184548428354$. Write $\Gamma_*$ for its periodic support orbit. There is an open interval $I\ni b_*$ and a tubular neighbourhood $U$ of $\Gamma_*$ in the four-dimensional support space with the following properties.

1. For every $b\in I$, the only complete orbit lying in $U$ at all arclengths is one periodic orbit $\Gamma_b$, up to phase. It has a primitive period $P(b)$, and its angle increment $2\pi h(b)$ over that period is strictly monotone in $b$.
2. All oriented geometric closed profiles with pitch in $I$ and complete support trace in $U$ are as follows. For $h(b)=a/d$ in lowest terms, $d>0$, there is one primitive reconstruction, up to rotation and arclength shift. Its primitive geometric length is $dP(b)$ and its turning number is $a$. Its positive integer covers give all further parametrised closed solutions at that pitch. For irrational $h(b)$ there is no closed reconstruction. The pitches of the primitive closed profiles in this tube form a countable dense set in $I$.
3. For any fixed turning number there are only finitely many such pitches, with no energy cap. More precisely, for $|m|\le10^{32}$ the only possible pitch is $b_*$. At $b_*$ the primitive geometric profile has turning number $-56$ and length $57P(b_*)$. In the chosen oriented tube the permitted $m$ in this range are exactly the negative multiples of 56. Reversing orientation gives the corresponding positive turning numbers in the reversed chart.

The radius of $U$ and width of $I$ are qualitative. The statement covers orbits with arbitrarily large closing length that remain in this tube, including perturbations with no prescribed cyclic symmetry. It places no bound on trajectories that leave the tube and return.

## A transverse multiplier calculation for the actual periodic orbits

The archived rotating-orbit certificate controls an actual family of periodic supports with midpoint parameters $c=(k_0,p_0,\ell,\alpha,b)$ in a cube of radius $r=10^{-32}$. The support recurs between $-\ell$ and $+\ell$. If the angle is $-112\pi/57+t$, with $|t|\le5\cdot10^{-35}$, the root is unique in that cube for this prescribed angle. The pitch is strictly decreasing and bi-Lipschitz as a function of $t$. These facts use the original two 4000-step enclosures and the contraction argument in [PitchAccumulation.txt](../../Pitch/PitchAccumulation.txt).

Let $A,B$ be the true four-by-four initial-support derivatives at the positive and negative half endpoints, at fixed pitch and fixed half-length. The derivative of the fixed-time full support return based at the negative endpoint is $AB^{-1}$, by the chain rule. Returning support coordinates suffice here because the angle is a separate reconstruction variable. The monodromy characteristic equation is $\det(A-\lambda B)=0$. No inverse of a numerical matrix is needed.

The two archived fundamental matrices have state order $(k,u,p,q,b,\theta)$. Their upper left four-by-four minors therefore enclose the proper support derivatives after adding the endpoint and parameter-motion error. The [analytic certificate](../classification_odd_branch_interval/AnalyticCertificate.txt), §§6–7, gives $K=2000$, $J=4000$, $|s|<32$, $\|D\Phi\|\le4K$, $\|(D\Phi)^{-1}\|\le4J$, $\|Df\|\le17$ and $\|D^2f\|\le4$ on the needed true trajectories. Variation of constants gives the uniform initial-data Hessian bound

\[
H=32(4K)(4J)4(4K)^2 .
\]

The midpoint initial state is a linear map of the parameters of norm at most one, and moving either half endpoint by at most $r$ adds a derivative error at most $17(4K)r$. Thus the recorded fundamental endpoint error plus $(H+17(4K))r$ is less than $10^{-12}$ in operator norm. Inflating each stored entry by $10^{-12}$ suffices uniformly over this family.

[The rational interval calculation](floquet.py) evaluates the 24-term determinant exactly at six rational arguments. The certified signs in increasing order of the test points are

| $\lambda$ | $-3$ | $-2$ | $-1/100$ | $-1/1000$ | $100$ | $110$ |
|---|---:|---:|---:|---:|---:|---:|
| sign of $\det(A-\lambda B)$ | + | − | − | + | − | + |

There is one real root in each of $(-3,-2)$, $(-1/100,-1/1000)$ and $(100,110)$. The fourth is exactly $+1$. Indeed the nonzero tangent vector $f_b(z(-\ell))$ is taken to itself by the derivative of the time-$2\ell$ return at the periodic orbit. It is nonzero everywhere by uniqueness, since the actual profile is nonconstant. The matrix $B$ is invertible by the flow property. Its characteristic equation has degree four, so all four roots are simple. The Poincaré section accordingly has one stable and two unstable directions. This calculation uses the true orbit derivatives throughout, including parameter uncertainty. The finite rational outputs are in [FloquetChecks.json](FloquetChecks.json).

## The certified block is a primitive support period

As proved in the certified branch analysis, $v=k_s$ satisfies $v'(0)<-200$ and $|v''|<4000$ along the orbit. Hence $v(s)<v(0)$ for $0<s\le1/40$. The primitive support period is larger than $1/40$. Every period is an integer multiple of the primitive period, since the nonconstant continuous periodic state has a discrete closed period group. If the certified block $2\ell<64$ contains $n$ primitive periods, then $n<2560$. Any $n>1$ would have a prime divisor $p\le2560$ for which $2\ell/p$ is a support period.

For each of these 375 primes, take $j$ nearest to $8000/p$. On the archived positive half grid its time is $s_j=j\ell_0/4000$, with $\ell_0$ the exact recorded centre. The true initial support is within $r$ of the central initial support, up to the recorded rounding error, and the true state at $s_j$ lies within $K\cdot2r$ of the stored grid state by §5 of the original analytic certificate. To compare to $2\ell/p$, allow time mismatch $|2\ell_0/p-s_j|+2r$. The componentwise derivative bounds for $(k,u,p,q)$ are $(36,39.4665625,72.25,73.25)$. These estimates apply also over the short endpoint extension furnished by the same certificate.

[The Arb replay](primitive.py) evaluates the original state-polynomial recurrence at all 4000 positive half-steps at the original precision. The state update, including each midpoint reset, is independent of the variational coefficients. The replay uses the same state arithmetic and order, thus generates the same nodes by induction. All six final displayed endpoint balls also match the original record byte for byte. Subtracting the timing allowance and an additional $10^{-27}$ for both state errors, at least one support coordinate at $2\ell/p$ differs from its initial coordinate by more than $0.01$ for each prime. The complete list is in [PrimitiveChecks.json](PrimitiveChecks.json). This excludes every divisor and proves $P=2\ell$ uniformly on our family.

## Why the family exhausts a neighbourhood

A compact, primitive, nonsingular periodic orbit is an embedded circle in support space. In a small tube take a transverse section at one phase. Projection to the original circle defines a phase coordinate with positive time derivative after shrinking the tube. Thus every complete orbit staying in the tube gives a full two-sided sequence of intersections with the section. Each successive intersection is given by the local first-return map $R_b$. This construction persists for nearby $b$ by transversality, the implicit function theorem, and compactness of a full traverse.

At the base orbit the derivative $A_0=DR_{b_*}$ has the three transverse multipliers above. The fixed point of $R_b$ continues uniquely by the implicit function theorem because $1$ is absent. It is also the only orbit of $R_b$ trapped in a small section ball, regardless of its period. To see this explicitly, translate the continued fixed point to zero and split $A_0$ into stable and unstable spaces. In an adapted norm, $\|A_s\|,\|A_u^{-1}\|\le \rho<1$. Uniformly on a small ball and nearby pitch, write $R_b(x)=A_0 x+g_b(x)$ with $g_b(0)=0$ and $\|g_b(x)\|\le\epsilon\|x\|$, where $\epsilon<1-\rho$. For an entire bounded orbit $x_j$, put $M=\sup_j\|x_j\|$ and use the maximum norm on the splitting. Iterating the stable equation from the infinite past bounds $\|x_j^s\|\le\epsilon M/(1-\rho)$. Iterating the unstable equation backwards from the infinite future gives $\|x_j^u\|\le\rho\epsilon M/(1-\rho)$. Therefore $M=0$. Shrink the flow tube so its section lies in that ball.

For every pitch in a sufficiently small interval inside the certified pitch image, the shooting family supplies a periodic orbit in this tube by continuous dependence. The isolation just proved identifies it with the unique continued orbit. We select nested tubes and then shrink the pitch interval so the entire continuing orbit stays inside the smaller tube for every remaining pitch. This proves exhaustiveness even for profiles with no imposed block symmetry.

## Closing the geometric profile and fixing the turning number

On the primitive support block the frame rotates through $2\pi h(b)$. The holonomy is strictly monotone by the certified pitch secants. If $h=a/d$ in lowest terms, the frame and supports both return after $d$ blocks. Conversely a geometric period of an arclength immersion returns both position and tangent, hence the support state, and is therefore an integer number of the primitive support periods. The frame then forces that integer to be a multiple of $d$. Thus the first geometric period has turning $a$. Irrational holonomy cannot close. This also proves uniqueness up to phase and plane rotation and accounts for all covers.

Here $|h+56/57|\le (5\cdot10^{-35})/(2\pi)<10^{-35}$, so $|h|>1/2$. At prescribed integral turning $m$, the only candidates are reduced fractions $a/d$ for which $a$ divides $m$ and $d<2|a|\le2|m|$, with $m/a$ a positive integer. Zero turning is impossible in the tube. There are finitely many candidates and strict monotonicity allows at most one pitch per fraction. If $a/d\ne-56/57$, integer separation gives $|a/d+56/57|\ge1/(57d)>1/(114|m|)$. For $|m|\le10^{32}$ this exceeds $10^{-35}$. Hence the only possible fraction is $-56/57$, attained once, at $b_*$. All conclusions follow.

## Scope of the classification

This computer-assisted mathematical proof uses the archived Arb trajectory and contraction bounds plus the two finite checks linked above. Two independently checked Lean modules establish the prime-divisor primitive-period criterion for the actual support trajectory and the six numerical determinant signs and three corresponding real roots for every pair of matrices inside the 32 certified input balls. The insertion of the analytic trajectory enclosures, the exact neutral multiplier and the geometric local-exhaustion argument remain in the mathematical proof. A finite energy cap controls the shooting data for all normalised profiles. The resulting compactness yields a finite union of pitch intervals and points, as in [EnergyCappedPitchSpectrum.txt](../../Pitch/EnergyCappedPitchSpectrum.txt). The present multiplier estimates do not control trajectories outside the one tube. Global finiteness would also need to exclude an entire closed branch with constant rational holonomy or another degeneracy elsewhere.
