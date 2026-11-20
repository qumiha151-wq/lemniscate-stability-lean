# Reproducing the local classification checks

Use the existing `OpenProblems/SolitonClassification` project. This package supplies two independently buildable Lean modules, two finite certifying calculations and the mathematical argument that connects them to the true periodic orbit. Its inputs are the original signed 4000-step records already present in the repository.

From this directory run the following with Python and the original integrator's Python FLINT dependency installed.

```text
python floquet.py
python primitive.py
python lean_centers.py
```

The first command evaluates exact rational determinant bounds. The second replays only the 4000 positive-time state updates at 100 decimal digits, compares the terminal state strings to the archive, and checks all 375 prime divisors. It records a coordinate witness and a positive lower bound for each divisor. The third verifies the numerical constants embedded in the Lean source against the signed archived endpoint matrices.

The analytic input directory is `../classification_odd_branch_interval/`. It contains `AnalyticCertificate.txt`, `shooting_certificate.json`, `metric_plus_o60_n4000.json`, `metric_minus_o60_n4000.json` and `validated_metric_shoot.py`. The finite numerical checks reuse those files directly. The strict monotonicity of the reconstructed angle and pitch correspondence is established in the project's `Pitch/PitchAccumulation.txt`.

From the `OpenProblems/SolitonClassification` project directory, the separate Lean check is

```text
lake build SolitonClassification.Rotating.PrimitiveSupportPeriod SolitonClassification.Rotating.FloquetPencil
```

The first module connects real endpoint matching to exact support periodicity. It proves that a positive period below 64 is primitive from the short-time exclusion and finitely many prime tests, and relates the proposed test times to rounded grid times. The second imports the project's rational-ball arithmetic and checks all six determinant signs by Lean kernel evaluation. It proves three real roots of the four-by-four determinant pencil for every pair of real matrices inside the displayed 32 coordinate enclosures.

The geometric theorem in `LocalClassification.md` uses both formal results. The application of the analytic error estimates to the true half-endpoint matrices and the true coordinate gaps on the intermediate grid nodes, the autonomous neutral multiplier, and the Poincaré isolation argument are justified in the computer-assisted mathematical proof. They have not yet been composed into an unconditional Lean theorem of local classification. The existing full shooting certificate's contraction result by itself does not identify a primitive period.

`GlobalJacobiObstruction.md` treats the separate issue of global finiteness. Its Jordan-chain calculation and the exclusions of scalar self-adjointness and a four-dimensional invariant symplectic form are mathematical arguments.
