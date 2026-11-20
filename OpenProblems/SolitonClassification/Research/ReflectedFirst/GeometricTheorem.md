# A zero-turn expander with a non-Bernoulli centre slope

The theorem `ClosedSimilarity.ReflectedArc.exists_first_zero_turn_expander`
has no shooting, smoothness or existence hypotheses. It gives a pair of real
numbers `b,T` and a smooth closed curve of period `4*T` satisfying
`0.719 < b < 0.720` and `5.70 < T < 5.71`. Its signed total curvature is
zero. At the expansion centre it has zero curvature with derivative `b`.
Every zero-curvature centre crossing of the very same initial curve has
absolute derivative `b`. Its normal support is not a cubic polynomial of
curvature (including lower degrees). Bernoulli's normalized law is
`p = -5 k^3 / 18`. The certified physical curve evolves by the full
pure-normal free elastic PDE and its length scales by `(1+4t)^(1/4)`.

Build from the SolitonClassification directory with

```sh
lake build SolitonClassification.FirstZeroTurnExpander
lake env lean SolitonClassification/AxiomAudit.lean
```

The first command includes three actual interval trajectories, their
outer-tube estimates and the event argument. The geometric bridge is in
ReflectedNumericGeometry, ReflectedPhysicalMarker and ReflectedPureNormal.
The ordinary project imports the same final theorem. Its axiom audit
includes the numerical namespace, the geometry and the rotating-flow
foundation. [Numerical method](README.md) · [Twelve-example interval proof](../ReflectedExpanders/ReflectedExpanders.md)
