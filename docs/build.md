# Building FormalOLP

FormalOLP uses Lean `v4.34.0-rc2`, Mathlib commit
`5fcc6656691ed31965746c369f41fa75e567ac9d`, and Tau Ceti commit
`8525a756ec80a2338bf75a42ca80f19c47ead468`. The dependency URLs and revisions
are pinned in `lakefile.toml`; `lake-manifest.json` records the resolved
transitive packages after the first `lake update`.

Install the pinned toolchain, resolve dependencies, and build the library:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake update
lake build FormalOLP
```

The `FormalOLP` library target includes modules below `FormalOLP/` and the
public root module `FormalOLP.lean`. Generated dependency sources and build
artifacts stay under `.lake/`, which is ignored by Git.

Run the cross-package compatibility smoke test separately. It first builds a
concrete Tau Ceti module, then imports that module alongside the public
FormalOLP root. Tau Ceti's package root is intentionally empty, so the concrete
module is the useful import-boundary check:

```sh
lake build TauCeti.Algebra.Algebra.Hom
lake env lean -E warning test/Compatibility.lean
```

The native FormalOLP gate is the library build, the warning-as-error check,
and the defining-module axiom audit.  Run these checks for every native topic
change:

```sh
lake build FormalOLP
lake env lean -DwarningAsError=true FormalOLP.lean
lake env lean -DwarningAsError=true test/FormalOLPAxioms.lean
scripts/check-native-integration.sh
scripts/check-native-integration-test.sh
```

`test/FormalOLPAxioms.lean` audits every declaration defined by a
`FormalOLP.*` module with `Lean.collectAxioms`; it allows only
`Classical.choice`, `propext`, and `Quot.sound`.  The native provenance check
verifies the declared integration files, their review hashes, the OLP source
and attribution references, and the absence of active `LeanPool` imports.

The former Lean Pool source staging was removed after native integrations were
completed.  The native declaration mapping and source guidance are recorded in
[`docs/lean-pool-provenance.md`](lean-pool-provenance.md) and
[`docs/lean-pool-integration.md`](lean-pool-integration.md).  The pinned source
snapshot, per-file hashes, and compatibility history remain historical records
under [`docs/archive/`](archive/README.md); they are not active build inputs.
