Linux follow-up for the rotating-pitch theorem

The input is the completed Q2 run that compiled the original two signed
4000-step grids. This job reads its proof objects, verifies them against the
Q2 receipts and compiles three more Lean 4.33.1 sources. It checks the exact
zero-premise theorem

SolitonClassification.Rotating.FullPitchAccumulation.exists_dense_positive_closed_rotating_pitches

The archived Q2 workflow stores assembly/compiled/checked, the assembly
reports, both validated input indices and graphs, and the assembly source
and logs. Its uploaded paths omit assembly/compiled/public_inputs. Those
missing project objects come from two retained sources. The nine
same-run batch artifacts contain 250 compact .public.tar.xz transports,
which yield 11,750 indexed .olean files. The original fixed Linux48 artifact
supplies 135 public objects (87 captured core plus 48 extension modules).
The new job verifies each primary object against the exact Q2 index and
each transport against the Q2 ledger. The 502 new module primaries come
directly from assembly/compiled/checked. The assembled theorem and its
ten concrete grid input names thereby remain available.

The restored Linux libraries come from release asset 742149339 at the
frozen archive and base-lock hashes. The 48-module Actions artifact is
14007325855; its archive and compiler report hashes are pinned. The prior
runner's absolute setup paths are obsolete. New setup JSON files map the
actual dependency graph to the newly restored public object paths, with
the fresh runner's external Mathlib and Lean paths. The three supplied
legacy sources have pinned hashes. Only a deterministic module/public-import
header, public visibility section and a final declaration-shape check are
added. Old project private layers and IR are unnecessary. The actual fresh
Lean counts are three for this job and zero for the original 503.

Run the installed workflow by dispatching the completed Q2 run ID. On a
research branch where workflow_dispatch is unavailable, publishing a new
OpenProblems/SolitonClassification/PitchLinuxFollowup/request.json
containing {"q2_run_id":"<the completed Q2 run ID>"} triggers it. No request
file is shipped in this package. The normal classification project does
not import this job. The original Q2 workflow and its sources are unchanged.

For a manual Linux replay with local copies, --assembly selects the
extracted assembly directory; its sibling fullmerge/ledger.json is used.
--parts selects the parent of the batch00 through batch08 directories.
--final48 selects the original final48 directory with compile_report.json
and public_inputs. --restored selects the core restoration directory with
base_args.json and base_lock.json. --sources selects the packaged sources.
Use --out for a new directory. These arguments are accepted by pitch_suffix.py.
If the original assembled runner or its complete public_inputs tree has
been preserved, --public-pool points to that tree instead of --parts and
--final48. This directly verifies the saved primaries without downloading
or unpacking the nine batches.
Verified results are saved to verified.json with per-module source hashes,
relocated setups, compiler output, objects and the final audit in suffix/.

An actual Windows Lean 4.33.1 test used the retained Linux48 .olean objects
from the cloud job, not Windows-built substitutes. It compiled both real
pitch modules and the final map with its ten grid inputs as explicit
parameters. Four original Linux shard transports yielded 188 verified
public primaries. See PilotEvidence.json. This test did not have the two
full concrete grids and does not verify the zero-premise result. Its success
establishes that the public import layout and final input types work.
