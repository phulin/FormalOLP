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
