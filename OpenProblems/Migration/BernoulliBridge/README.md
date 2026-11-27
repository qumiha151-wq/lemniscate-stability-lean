# Migration near a covered Bernoulli lemniscate

For every cover number $M\geq 1$ and every $0<r<\sqrt{2}/4$, there is an initial curvature-profile neighborhood on which all nonnegative-time slices contain the same closed disk of positive radius in their convex hulls. The center is chosen at initial time. At time $t$ the hull contains the closed disk of radius $r(a^4+30t)^{1/4}$ about this center, where $a$ is the initial length divided by the reference cover length.

The main theorem `Lemniscate.bernoulli_nonmigration_from_initial_curvature` supplies existence of a smooth free elastic flow and applies to every smooth flow with that initial immersion. Its hypotheses use the intrinsic signed curvature-profile deviation. The proof obtains the all-time height estimate from the original stability project's parabolic segment bound and identifies these normal graphs with every geometric solution.

Build from this directory in a checkout of the research branch using `lake build`. The two local dependencies are the independent Migration project one level up and the original stability project at the root. Both use Lean 4.33.1 and the same pinned mathlib revision. [Main theorem](BernoulliBridge/BernoulliNonmigration.lean) · [Axiom audit](BernoulliBridge/AxiomAudit.lean) · [Verification record](Verification.json)
