# First reflected pure-expander shooting root

The shooting equations use the pure expansion coefficient one, starting at
$(k,k',p,q)=(0,b,0,0)$. The tested slope interval is
$0.719266732593\pm10^{-8}$. The event time lies within $10^{-4}$ of
$5.70216430671656$. The endpoint equations are $k'=q=0$.

The Lean modules reuse the SolitonClassification six-coordinate polynomial
field $(k,k'/8,p,q,\omega,\theta)$ with $\omega=0$. The proof for the first
root uses only the four physical state coordinates. The existing polynomial
and remainder theorems instantiate at order 20 on a fixed integer mesh
$10^{28}$. An analytic error of $10^{-19}$ at each true ODE step is included
in the integer radius.

The three shots use 740 steps to the same reporting time. The wide initial
box controls the whole slope range. The independent endpoint shots give
opposite signs of $q$ at the velocity-zero events. Over the whole event
interval the actual equations imply $\partial_t k'\ge3$ and
$|\partial_t q|\le1$. The implicit event time is continuous by a direct
transversality estimate. No numerical state derivative is required.

Run the following command from the SolitonClassification project directory.

```text
lake build SolitonClassification.Reflected.FirstRoot
```

The deterministic integer generator produces three complete traces and
groups their steps into 111 kernel-proof modules plus three assembly
modules. Each individual arithmetic equality is reduced by
`decide +kernel`. The final module prints the zero-premise theorem's
dependencies and audits every declaration in its namespace. Running
`python Research/ReflectedFirst/produce.py --dest SolitonClassification/Reflected --size 20`
from the same project directory regenerates the 114 trajectory source files.

The local exact-integer mirror is independently executable with
`python mesh_replay.py`. Floating-point values printed for convenience
appear only after the exact integer operations. A successful mirror run
and a completed kernel build have separate receipts. The reference proof
uses the ordinary Lean 4.33.1 kernel and the project's pinned mathlib.
