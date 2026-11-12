# Verified centroid-escape certificate

The complete proof was checked at `9ef471f7e818029931ad20abaa1119a08819b718` in [run 43214648337](https://github.com/qumiha151-wq/lemniscate-stability-lean/actions/runs/43214648337). All 75 concrete shards and the 152-module assembly passed. The final audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

Final theorem: `CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.Certificate.smooth_FEF_centroid_escape`.

It asserts existence of a smooth closed immersed classical free elastic flow with unbounded arclength centroid. It does not assert migration away from every compact set, unrestricted length growth, or a soliton classification.

This directory permanently preserves the exact checked Lean sources, manifests and logs. It omits compiled binaries. The archival job verifies source, binary and log hashes before copying these files; it is not a new kernel run. Source hashes are listed in `archive_inventory.json`.

Reproduction uses the independent CentroidEscape Lake project and its pinned Lean/mathlib version. Build its core first. Compile all 75 `shards/*/manifest.json` with `tools/compile_shard.py`, using the same `.lake/build/lib/lean` output directory. Then run `tools/compile_full_assembly.py` with this directory's `assembly/manifest.json`, `--manifest-list` pointing to this directory's `manifest-index.json`, and `--candidate-source CentroidEscape/CandidateEndpointChecks.lean`. The path overrides relocate original CI paths; all sources and manifest hashes remain checked. All CentroidEscape compiled modules must share one build root. The full workflow provides the exact bounded compilation commands.
