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
  validity; `NaturalDeduction` defines the derivation object and proves its
  full native soundness chain. Completeness remains open.
- Set theory: `FormalOLP.SetTheory.Basic` defines the membership language and
  realizes extensionality, empty-set, pair, and singleton uniqueness at the
  model level. It does not formalize full ZF/ZFC axiom schemata.
- Normal modal logic: native K/T/D/4 Kripke validity and frame facts, extended
  with B and 5 correspondences under symmetry and Euclideanity.
- Normal modal extensions: native B/5 frame correspondences under symmetry and
  Euclideanity.
- Propositional/proof theory: native valuation semantics and finite-support
  N2c natural deduction soundness.
- Applied modal, counterfactual, second-order, model-theory, Turing-machine,
  and Robinson-Q topics each have an initial checked native or Mathlib-backed
  chain; their theorem-level boundaries are recorded in the provenance ledger.
- Computability: native relative recursion, many-one set reductions, and
  Turing-reducibility support; the machine/`RecursiveIn` equivalence remains
  open.

Every row in the provenance ledger identifies the OLP source path, exact Pool
source family used as guidance, native declarations, and proof boundary.
Native modules have no Lean Pool imports.
