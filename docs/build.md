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
lake build
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
