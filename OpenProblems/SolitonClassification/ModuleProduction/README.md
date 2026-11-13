# Isolated rotating certificate module project

This source-only project is independent of the legacy SolitonClassification
build and every other open problem. It contains the frozen 87 generic module
sources and a fresh audit importing all private generic declarations. There
are no precompiled artifacts and no claim of a Linux build or a full shooting
root from packaging these files.

The numerical 32-step module shard and a separate portable public-only consumer
have actually passed on Windows. The consumer reports only actual child wall
time and exit status, with no inferred CPU or peak-memory value. This package
does not claim that those runs were Linux executions; the Linux pilot must
rebuild its own generic core and capture its own actual compiler/library lock.

The toolchain is Lean 4.33.1; the exact Mathlib and transitive dependency
revisions are fixed by the accompanying Lake manifest. After obtaining the
dependencies and their matching Mathlib cache, build and audit this project:

```sh
lake build
lake env lean SolitonClassification/Rotating/ModuleFullGenericAudit.lean
```

Use explicit portable paths for data generation. These commands only propose
data and source; the strict compiler must subsequently kernel-check them.

```sh
python3 tools/plan_production_grid.py --seed inputs/shooting_certificate.json \
  --candidate-source inputs/CandidateInitial.original.lean \
  --template-root inputs/templates --output plan --revision "$GITHUB_SHA" \
  --steps-per-sign 4000 --shard-size 32
python3 tools/generate_production_shard.py --key RP0000 --count 32 --sign 1 \
  --seed inputs/shooting_certificate.json \
  --candidate-source inputs/CandidateInitial.original.lean \
  --template-root inputs/templates --module --output generated/RP0000
```

For later shards also pass the exact input checkpoint from the pinned plan.
The original CandidateInitial bytes define the candidate hash; the separately
wrapped module source has a different file hash and must not silently replace
this canonical input. The exact Lean initial condition and all state/matrix
boundary equalities remain mandatory proof obligations.

The pipeline locks the actual Linux base once and reuses its exact bytes for
every shard. The Windows lock is not a Linux artifact. Complete checked source,
log, public, private and server files must be preserved in durable shard
archives. Final aggregation should validate one archive at a time, retaining
only public inputs in the aggregation search path and using an explicit
official importArts setup; it must not unpack every private archive at once.
The final consumer itself must use Lean's module system.

The environment helper must run inside `lake env` after the generic build and
fresh all-private audit. It preserves the real library search order, resolves
the actual compiler behind the toolchain shim, requires all 88 generic primary
artifacts and their sidecars, and rejects another root shadowing the project
namespace. The portable consumer validates the original complete bundle and
locked base before and after its separate public-only Lean invocation. Its
output tree must be fresh and separate from both the bundle and base libraries.
The local `.gitattributes` disables checkout newline conversion because source
inventory hashes bind exact bytes, including any existing line endings.

The package's default target contains only the generic core. Future generated
shards, exact cross-shard seams, actual-flow bounds and finite shooting checks
are separate verification work. A certified example would not by itself
classify every soliton in the paper.
