V3 original-shard release tools: reviewed local implementation

Package/ is the byte-identical immutable tools package. Start its entry point
as Python -I -S -B Package/launcher/launch.py, with Package/ as --package-root.
The eighteen runtime helpers remain flat under Package/runtime; the launcher
is its sibling. Package/package_manifest.json is unchanged from the reviewed
v2 package (SHA e829412c3bd9fea644288cc7e30cdbf36ca0b6e1503dd797ae8b57c297f4b5f5).

ReviewEvidence/ is external evidence, intentionally outside that package's
exact inventory/import path. It contains the two new fixture sources and
reports, all fourteen real isolated-subprocess stdout/stderr pairs, the
supplemental actual rejected --execute trace/stdout/stderr, frozen indexes,
and root's final review. Large synthetic fixture directories and originals
are not duplicated. Their absence is not a claim of new end-to-end replay.

Actual checks include local committed Git identities, -I -S -B import
isolation, corruption rejection, compact evidence formatting and a fixture
request rejected at controller.prepare before execute. Positive production
execute has not run. Success-format evidence in the supplement is explicitly
synthetic, not actual controller/HTTP success. Windows symlink creation was
unavailable and that actual-link test was not exercised.

There is no remaining246 production catalog, real release request, deployment
workflow, remote mutation, new Lean computation or complete theorem claim in
this stage. Tools commit P must be published and independently checked before
the later Q inputs/workflow can pin it. The manifests contain no self-hash or
future P/Q revision. Token is read only from environment at real execution.
