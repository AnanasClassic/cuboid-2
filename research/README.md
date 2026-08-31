# Research archive

This directory preserves the exact certificate generators, intermediate
models, independent checks, unsuccessful approaches, and superseded proof
routes developed during the project.

The current result is not open: Sharipov's second cuboid conjecture is proved,
and the final irreducibility theorem is formalized in Lean. The authoritative
entry points are:

- the [repository overview](../README.md);
- the [Lean project](../lean/README.md);
- the [formalization status](../lean/FORMALIZATION_STATUS.md);
- the public theorem in [`Cuboid2/Main.lean`](../lean/Cuboid2/Main.lean).

Individual subdirectory README files are retained as technical records of the
workstream that produced them. Some describe blockers or next steps that were
accurate for that route at the time. Unless a file explicitly says otherwise,
those statements are historical and must not be read as the current status of
the theorem or the Lean formalization.

The external generators and JSON artifacts are useful for independent replay
and audit, but they are not unchecked proof premises. Lean rechecks the
identities and finite statements used by the public theorem. See
[`scripts/reproduce_lean.sh`](../scripts/reproduce_lean.sh) for the strict Lean
gate and [`scripts/reproduce.sh`](../scripts/reproduce.sh) for the larger
external arithmetic replay.
