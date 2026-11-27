# The ordinary equation after descent from a finite power cover

Let \(s=s_0+w^q\) with an integer \(q\ge1\). Suppose that at every point of a punctured disk \(0<|w|<r\), a function \(f(w)\) agrees locally with the pullback of an analytic scalar curvature germ satisfying the fourth-order similarity equation at that point. These local germs may vary from point to point. No growth estimate at \(w=0\) is assumed.

Then there is a meromorphic germ \(G\) at \(s_0\) such that \(f(w)=G(s_0+w^q)\) on a punctured neighborhood of zero. At every sufficiently close \(s\ne s_0\), the representative \(G\) is analytic and satisfies
\[
 2(GG^{(4)}-G'G''')+3G^2(G')^2+5G^3G''+G^6-2aG^2-2bG'=0 .
\]
This conclusion holds for arbitrary complex \(a,b\). [Lean theorem for the descended solution](../../SolitonClassification/RamifiedBaseResidual.lean)

If \(a>0\) and \(a,b\) are real, the end has one of the following forms.

* **Analytic filling.** There is an analytic germ at \(s_0\) agreeing with \(G\) off the center and satisfying the scalar equation at \(s_0\) itself.
* **Simple pole.** For some \(c\in\{3i,-3i\}\) and \(R\) analytic at \(s_0\),
  \[
  G(s)=\frac{c}{s-s_0}+(s-s_0)^3R(s).
  \]
  The defect \(G''+2G^3/9\) extends analytically to \(s_0\), where its value is zero.

Both alternatives apply to the germ in the original complex arclength variable. [Lean theorem for ordinary ends](../../SolitonClassification/RamifiedOrdinaryEnd.lean)

The proof first obtains a finite Laurent principal part on the covering disk from a Cauchy estimate on ordinary charts. The scalar equation forces all deck rotations to fix this meromorphic germ. A power-cover descent theorem gives a base representative. At a nonzero lift \(w\), choose the local analytic inverse to \(z\mapsto s_0+z^q\) taking \(s_0+w^q\) to \(w\). Composing both the covering representation and the given ordinary chart with this inverse identifies their base germs. All four derivatives consequently agree. The removable case follows by continuity of the analytic residual, and the pole case uses the ordinary Laurent resonance equations. [Finite principal part](../../SolitonClassification/RamifiedFinitePrincipal.lean) · [Deck invariance](../../SolitonClassification/RamifiedScalarContinuation.lean) · [Power descent](../../SolitonClassification/RamifiedDeckDescent.lean) · [Ordinary Laurent calculation](../../SolitonClassification/MeromorphicPoleExtension.lean)

The complete local theorem also permits meromorphic ordinary charts throughout the punctured cover. Their poles may initially accumulate toward the exceptional value. Reflection near an ordinary pole gives a base meromorphic filling in this case. The descended solution still has the ordinary residual and the same removable or simple-pole alternatives. [General isolated-end theorem](../../SolitonClassification/RamifiedIsolatedOrdinaryEnd.lean)

The passage from pathwise finite monodromy to power coordinates, and the global continuation argument over a closed locally finite exceptional set, are written proofs. [Finite branching and global continuation](FiniteBranchContinuation.md)
