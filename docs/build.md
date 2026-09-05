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

The vendored Lean Pool snapshot is a local `LeanPool` library with nine
explicit entry roots.  Verify its path and hash inventory before building the
entries:

```sh
scripts/check-leanpool-provenance.sh
lake build LeanPool.Computability LeanPool.FoZfc \
  LeanPool.FormalizationOfBoundedArithmetic LeanPool.Incompleteness \
  LeanPool.PartialCombinatoryAlgebras LeanPool.ZFLean \
  LeanPool.Lean4GlCoalgebras LeanPool.LeanModelChecking LeanPool.Lentil
lake env lean -E warning test/LeanPoolCompatibility.lean
lake env lean -E warning test/LeanPoolAxioms.lean
```

The Pool snapshot was authored against a different Mathlib revision.  The
Recorded compatibility import changes are listed in the provenance manifest;
inherited deprecation warnings and any slow upstream declarations
remain visible in the entry build output.  The aggregate smoke test also
imports `TauCeti.Algebra.Algebra.Hom` to exercise the concrete Tau Ceti
boundary.  The full aggregate remains pending if a vendored entry has not
finished building; the current Incompleteness Metamath closure includes a
resource-intensive inherited declaration.

Current vendor verification has eight passing entry builds: Computability,
FoZfc, FormalizationOfBoundedArithmetic, PartialCombinatoryAlgebras, ZFLean,
Lean4GlCoalgebras, LeanModelChecking, and Lentil.  The Incompleteness entry
remains blocked while the inherited `Formula`/`Functions` performance issue is
investigated.  The aggregate compatibility smoke test has not passed yet.

`test/LeanPoolAxioms.lean` walks the declarations recorded in each imported
`LeanPool.*` module and checks their transitive axioms with
`Lean.collectAxioms`.  It permits only `Classical.choice`, `propext`, and
`Quot.sound`; it reports `sorryAx` and all other axioms as failures.  While
the Incompleteness entry is unavailable, the same audit with that import
removed passes for 11,836 declarations.  Run the documented command after
all nine entry roots have built for the complete snapshot.
