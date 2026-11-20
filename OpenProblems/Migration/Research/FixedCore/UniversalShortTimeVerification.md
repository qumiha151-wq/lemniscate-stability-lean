# Formal verification of the uniform short-time disk

The statements belong to the independent **Migration** project. The final inclusions use Lean’s `Metric.closedBall` and `convexHull ℝ` of the image of one actual material period.

| Module | Checked statement |
| --- | --- |
| `Migration.MaximumAreaCenter` | For a compact subset of the plane with directional widths at least \(W>0\), a center obtained from a maximum-area triangle has support depth at least \(W/3\) in every unit direction. |
| `Migration.DirectionalWidth` | The smooth regular position, its signed curvature, bending and unitary rotations give \(E W(e)\ge2\) in all unit directions. |
| `Migration.SupportRecession` | A support decrease by \(\eta/E_s\) costs \((t-s)E_s^3(E_s-E_t)\ge\eta^3/(\pi+\sqrt{2\eta})^2\). The underlying finite-time estimate uses the position-defined elastic flow, actual force dissipation and arclength cutoff mass. |
| `Migration.UniversalShortCore` | One center works for all admissible radii and stopping times on a smooth physical slab. The common physical radius \(1/(3E_s)\) has the physical time threshold \(1/[27(\pi+\sqrt{2/3})^2]\) after multiplication by \(E_s^4\). |
| `Migration.InitialDirectionalWidth` | The continuous forward limits of the directional height extrema and physical bending give the same all-direction width estimate at time zero. |
| `Migration.ForwardShortCore` | The energy-drop theorem and the explicit short-time disk include the actual initial slice with the PDE imposed for \(t>0\). The endpoint inputs are joint right continuity of position and right continuity of bending. |
| `Migration.RoundPartitionCost` | For the time and energy functions of a once-covered expanding circle, every subdivision with certified worst-case recession budgets \(d_j\) satisfies \(\sum d_j\ge2(R_\mathrm{last}-R_\mathrm{first})\). The module checks the scalar inequality and its finite telescoping sum. The circular solution and its physical energy are calculated in the manuscript. |

The center and the static range, arclength mass, rotational invariance, endpoint estimates and energy ceilings are proved within these modules or their existing Migration dependencies. The final theorems impose neither a turning-number condition nor a bound on energy times length. They do not decide whether an actual closed flow can migrate across a line at arbitrary times.

The [mathematical proof](UniversalShortTimeDisk.md) gives the mechanism and constants. The [verification record](ShortTimeVerification.json) identifies the checked sources, compiled objects and root audit.
