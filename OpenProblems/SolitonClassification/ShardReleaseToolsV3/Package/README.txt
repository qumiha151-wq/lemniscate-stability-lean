Rotating shard release tools v3: local library/launcher package.

The runtime directory contains exactly 18 frozen helpers. The launcher is a
sibling, and requires Python -I -S -B plus an externally pinned manifest SHA
and actual committed tool revision. Token is read only from GH_TOKEN.

This package creates no real remaining246 catalog, release request or Actions
workflow. Its manifest has no self-hash or P/Q. Root must independently verify
the actual tool commit and the later input/workflow commit before execution.

Tests in evidence distinguish orchestration stubs, local Git identity, local
archive bytes, in-memory HTTP, and actual Lean/cloud evidence. No local test
is promoted to a live release. Large raw fixtures remain in the author's
workspace/original durable archives and are not silently embedded here.

Success compact evidence excludes original ZIP/tar bodies; failure recovery
lists safe original tar paths without copying or deleting those originals.
Evidence retention in Actions is temporary. Complete classification and the
full numerical theorem are not claimed by this publication tool package.
