# Native reuse plan

FormalOLP integrates mathematics into its own topic modules. Lean Pool source
is used as pinned proof guidance, with explicit OLP statement mapping and
native definitions. Native modules do not import Lean Pool namespaces.

The temporary source staging was retired after the current native chains were
checked. Its immutable source audit and per-file hashes remain in
[`archive/`](archive/README.md), while current integration status is in
[`lean-pool-provenance.md`](lean-pool-provenance.md).

## Current native chains

- `SetsFunctionsRelations.Functions`: domain/codomain-aware composition and
  inverse consequences using Mathlib `Set` APIs.
- `IntuitionisticLogic.Kripke` and `Soundness`: partial-order Kripke forcing,
  persistence, and elementary semantic axiom/rule validity. `NaturalDeduction`
  now supplies the separate intuitionistic derivation object and full
  soundness chain; completeness remains pending.
- `SetTheory.Basic`: membership language realization, extensionality, and
  empty-set, pair, and singleton existence/uniqueness consequences at the
  model level. Full ZF/ZFC axiom schemata remain pending.
- `NormalModalLogic`: native K/T/D/4 Kripke semantics and frame facts.
- `PropositionalLogic` and `ProofTheory`: native valuation semantics and the
  finite-support N2c derivation/soundness chain.
- `AppliedModalLogic`, `Counterfactuals`, `SecondOrderLogic`, `ModelTheory`,
  `TuringMachines`, and the Robinson-Q part of `Incompleteness`: each now has
  a checked initial native or Mathlib-backed chain recorded in the provenance
  ledger.
- `Methods`: reusable weak, strong, well-founded, and measure induction
  principles are now checked; the remaining proof-methods prose is pending.
- `Computability.RelativeComputability` and `TuringReducibility`: staged
  relative recursion, many-one set reductions, and Turing-reducibility
  support. The machine/`RecursiveIn` equivalence remains pending.

`Methods`, the K3 fragment of `ManyValuedLogic`, and the indexed De Bruijn
foundation of `LambdaCalculus` now have checked native chains. Lambda's named
syntax, Church--Rosser, normalization, and definability interfaces remain
pending.

Each integration records the OLP source path, the exact Pool declaration
family used as guidance, native declarations, and a proof boundary. Future
work must add a concrete bridge row before claiming a source family is
integrated.

## Scaffold completion audit

The original scaffold in commit `bcc4f89` introduced seventeen mathematical
topic roots. The current `FormalOLP.lean` imports all seventeen named
aggregators, and each aggregator imports a native child containing definitions
and a checked theorem chain. The exact file-to-source mapping is in
`docs/topic-map.md`; the proof-bearing file inventory and SHA-256 checks are in
`docs/native-integration-manifest.tsv`. The provenance checker reports 24
registered native files and rejects omitted rows, hash changes, active
`LeanPool` imports, and missing attribution references.

This is scaffold completion at the repository's foundation level. It does not
claim completion of the Open Logic Text. The ledger records the remaining
chapter-level gaps: first-order proof-system completeness; modal Hilbert
systems/canonical completeness; intuitionistic completeness; full ZF/ZFC;
arithmetization, representability, and incompleteness beyond Robinson Q;
concrete-machine/`RecursiveIn` equivalence; model-theory interpolation and
Lindström results; temporal logic; second-order function variables and
metatheory; many-valued systems beyond K3; lambda Church--Rosser,
normalization, and definability; counterfactual sphere representation; and
proof-theory cut elimination and normalization.

The native integrations deliberately contain no active LeanPool imports. The
dependency graph is pinned by `lakefile.toml` to the recorded Mathlib and Tau
Ceti revisions, and `docs/native-integration-manifest.tsv` distinguishes
Pool-guided `native-adaptation` files from newly authored `native-olp` and
Mathlib-backed `native-mathlib` files. Open Logic CC BY 4.0 attribution and
the preserved Pool license/notice records are kept separate from any future
license decision for newly authored Lean code. The completed foundation gates
are the full library build, warning-as-error root check, declaration axiom
audit, compatibility smoke test, and native provenance/negative fixtures.

## Verification

Run the native checks after changes:

```sh
lake build FormalOLP
lake env lean -DwarningAsError=true FormalOLP.lean
lake env lean -DwarningAsError=true test/FormalOLPAxioms.lean
lake env lean -E warning test/Compatibility.lean
```

The historical vendor checker and Lean Pool targets were removed with the
temporary source tree. They are documented only in the archived audit.
