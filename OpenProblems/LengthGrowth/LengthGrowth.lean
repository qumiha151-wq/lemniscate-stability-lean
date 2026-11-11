import LengthGrowth.ScalarDissipation

/-!
Length-growth question: PARTIAL ANALYTIC REDUCTION ONLY.

`FreeElasticScalar.secant_sq_le_energy_drop` derives a finite-interval
secant bound from explicitly assumed scalar derivative and dissipation
hypotheses. The free-elastic-flow PDE, its variation formulae, and the
unrestricted quarter-power upper bound are not formalized here.

`FreeElasticScalar.conditional_fourth_power_bound` uses the intermediate
value theorem and assumes the restart estimate and a uniform bound on
E(s)*L(s). It proves L(t)^4 <= max ((2*L(0))^4) (16*K^2*t), without
assuming monotonicity of length. The uniform normalized-energy bound
remains a hypothesis, not a proved property of every geometric flow.

Run this independent project from its own directory:
  lake +leanprover/lean4:v4.33.1 update
  lake +leanprover/lean4:v4.33.1 exe cache get
  lake +leanprover/lean4:v4.33.1 build

This project does not import the stability or migration projects.
-/
