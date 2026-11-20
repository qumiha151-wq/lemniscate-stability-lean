# Closed rotating elastic-flow profiles

Lean 4.33.1 verifies a closed, nonconstant-curvature rotating elastic-flow solution. A second theorem proves that a positive interval contains a dense set of pitches realized by closed rotating profiles with nonconstant curvature. The classification of all free elastic flow solitons remains open.

| Result | Lean declaration | Evidence |
| --- | --- | --- |
| Closed rotating elastic flow | `SolitonClassification.Rotating.FullCandidate.exists_closed_rotating_elastic_flow` | [Kernel report](evidence/assembly_report.json), [independent readback](evidence/VerifiedCandidate.json), [fresh axiom audit](evidence/CandidateAudit.log) |
| Dense positive pitches | `SolitonClassification.Rotating.FullPitchAccumulation.exists_dense_positive_closed_rotating_pitches` | [Verified theorem](evidence/PitchVerified.json), [independent readback](evidence/VerifiedPitch.json), [fresh axiom audit](evidence/PitchAudit.log) |

The first run checked 502 source modules plus an independent application of the theorem without hypotheses. Its axiom audit covered 105,287 declarations. The second run checked three more modules using the first run's concrete positive and negative grid certificates. Both final checks permit only `propext`, `Classical.choice` and `Quot.sound`. [Candidate workflow](https://github.com/qumiha151-wq/lemniscate-stability-lean/actions/runs/44650976356) · [Pitch workflow](https://github.com/qumiha151-wq/lemniscate-stability-lean/actions/runs/44657378217)

The proof release contains the exact original candidate and pitch ZIPs, the original 48-module supplement ZIP and nine projection ZIPs. The manifest records the SHA-256, byte length, producer job and source run of each ZIP. The release asset `rotating-proof-asset-receipt.json` gives the twelve release asset IDs and hashes verified after download. The complete original archives for the 250 signed shards remain available under their earlier releases, with their asset IDs in the candidate index. [Proof release](https://github.com/qumiha151-wq/lemniscate-stability-lean/releases/tag/rotating-closed-profiles-2026-11-20-v1) · [Source artifact manifest](origins.json) · [250 original archive records](../FullCandidateExecution/index.json)

The [candidate workflow](../../../.github/workflows/rotating-full-candidate.yml) and [pitch workflow](../../../.github/workflows/rotating-pitch-after-full.yml) contain the exact replay commands. The [pitch package](../PitchLinuxFollowup/Readme.txt) describes how to reconstruct the public Lean inputs from the archived ZIPs and the original core release.
