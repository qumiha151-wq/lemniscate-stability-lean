# What remains for a global finite-pitch theorem

Suppose a finite cap on $EL$ contains infinitely many distinct pitches of noncircular closed profiles. Compact semianalytic shooting data then yield a smooth, locally analytic arc of genuinely closed curves parametrised by their pitch $b$ on an open interval, as shown in [the energy-cap argument](../../Pitch/EnergyCappedPitchSpectrum.txt). The following obstruction uses the Jacobi operator of the **full closed geometric curve**, including all periods necessary for closure. It is stronger than merely asking for a singular support return at the end of one block.

At each point of this arc, with arclength derivative $D$ and supports $p=X\cdot N,q=X\cdot T$, write

\[
\mathcal{J}\phi=D^4\phi+
 D\left(\tfrac52 k^2 D\phi\right)
 +(bp-q)D\phi+
 \left(3k_s^2+4kk_{ss}+\tfrac32 k^4+1\right)\phi .
\]

The periodic fourth-order operator has a nontrivial Jordan chain at zero. More precisely,

\[
\mathcal Jq=0,\qquad \mathcal J\phi=-q,\qquad q\not\equiv0
\]

for some smooth periodic $\phi$. To see this, differentiate $F+p+bq=0$ with $F=k_{ss}+k^3/2$. The curve variation may be taken in a fixed parameter so varying arclength period supplies no boundary term. A tangential component differentiates the identically zero soliton residual in the tangential direction. For normal variation $\phi N$, the standard directly differentiated formulas are

\[
\delta D=k\phi D,\quad \delta k=\phi_{ss}+k^2\phi,
\quad\delta p=\phi-q\phi_s,\quad\delta q=p\phi_s .
\]

Substitution yields the displayed operator and, because the branch parameter is $b$ itself, gives $\mathcal J\phi=-q$. Rigid rotation preserves the residual and has normal component $q$, proving $\mathcal Jq=0$. If $q\equiv0$, then $D|X|^2=0$ and the regular immersed curve lies on a circle about the chosen origin. This possibility was excluded. In particular the analytic branch would have to satisfy $\int q\eta\,ds=0$ for every element of the adjoint periodic kernel. A proof that every full closed noncircular profile admits some adjoint nullvector with nonzero pairing against $q$ would imply finiteness in every cap. Failure of this pairing at a point by itself gives no analytic arc.

Two structural tests explain why readily available conservation laws do not establish that missing assertion.

* Write $d=bp-q$. The formal antisymmetric part in arclength measure is $\mathcal J-\mathcal J^*=2dD+d'$. A positive weight that made this differential expression formally symmetric would have to be constant, by comparing the third-order terms in $(\mu\mathcal J)^*$ and $\mu\mathcal J$. It would then require $d=0$. On a periodic orbit at nonzero $b$, $q=bp$ would give $1+kp=q'=bp'=-bkq=-b^2kp$, hence $p'=b/(1+b^2)$, contradicting periodicity. Thus an arclength-density change cannot produce a self-adjoint full Jacobi operator at any nonzero pitch.
* The fixed-pitch support vector field has zero divergence, so its full time return preserves volume. A symplectic return in four real dimensions, for any nondegenerate skew form on that tangent space, would have reciprocal spectrum with even algebraic multiplicity at $+1$. Indeed the degree-four characteristic polynomial is palindromic, which gives $P'(1)=2P(1)$. At the actual rotating orbit, $+1$ is a **simple** eigenvalue by [the certified multiplier calculation](LocalClassification.md). Hence the fixed-time support return on this four-dimensional state space cannot preserve any nondegenerate skew form there. In particular there is no smooth invariant symplectic form on a neighbourhood of this support orbit. An extended phase space is a different possibility and would require an additional argument on the projected solutions.

These obstructions apply to all full geometric curves in the putative pitch arc. Showing that the Jordan chain is impossible at one point on every such arc, or excluding every such arc by another mechanism, remains necessary for the global conclusion.
