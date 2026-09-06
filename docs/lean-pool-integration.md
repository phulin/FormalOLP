# Native Lean Pool guided integrations

This is the short working index for theorem-level integrations. The detailed
provenance and licensing record is in
[`lean-pool-provenance.md`](lean-pool-provenance.md); historical vendor
hashes are in
[`archive/lean-pool-vendor-manifest.tsv`](archive/lean-pool-vendor-manifest.tsv).
The current native-file hash/source check is
[`native-integration-manifest.tsv`](native-integration-manifest.tsv).

Current native chains are:

- Sets/functions: `FormalOLP.SetsFunctionsRelations.Functions` proves
  codomain-preserving composition and inverse consequences with Mathlib
  `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, and `Set.BijOn`.
- Intuitionistic semantics: `FormalOLP.IntuitionisticLogic.Kripke` proves
  persistence of forcing; `Soundness` proves elementary semantic axiom/rule
  validity. It does not define natural-deduction derivations or full ND
  soundness.
- Set theory: `FormalOLP.SetTheory.Basic` defines the membership language and
  realizes extensionality, empty-set, pair, and singleton uniqueness at the
  model level. It does not formalize full ZF/ZFC axiom schemata.
- Normal modal logic: native K/T/D/4 Kripke validity and frame facts.
- Computability: native relative recursion and Turing-reducibility support;
  the OLP machine/many-one equivalence remains open.

Every row in the provenance ledger identifies the OLP source path, exact Pool
source family used as guidance, native declarations, and proof boundary.
Native modules have no Lean Pool imports.
