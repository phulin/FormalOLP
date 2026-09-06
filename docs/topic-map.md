# FormalOLP topic map

FormalOLP follows the subject-level parts in the Open Logic Text and uses
native Lean module names.  The map intentionally has no chapter numbers:
source chapters and sections can change independently of the Lean API.

The current OpenLogic source is the initialized submodule at commit
`1e960beff9ed7835bf3e3f1335e21af3439cd107` from
<https://github.com/OpenLogicProject/OpenLogic>.  The table records the actual
source roots used to derive each aggregator.  A module marked “scaffold” has
scope documentation only; “initial API” identifies the checked native
declarations currently proved in Lean.

Each mathematical topic currently has one flat entry module under
`FormalOLP/`.  Future declarations can be organized in a same-name child
directory, such as `FormalOLP/FirstOrderLogic/`, without changing the public
topic entry point.  Editorial source parts that do not define a mathematical
Lean API remain mapped below as documentation-only material.

| Lean module | OpenLogic source path(s) | Current scope |
| --- | --- | --- |
| `FormalOLP.SetsFunctionsRelations` | `OpenLogic/content/sets-functions-relations/sets-functions-relations-complete.tex`; `sets/`; `relations/`; `functions/`; `size-of-sets/`; `arithmetization/`; `infinite/` | Initial API: set absorption and native function composition/inverse chain; remaining source topics scaffolded |
| `FormalOLP.PropositionalLogic` | `OpenLogic/content/propositional-logic/propositional-logic.tex`; `syntax-and-semantics/` | Initial API: native propositional formula syntax |
| `FormalOLP.FirstOrderLogic` | `OpenLogic/content/first-order-logic/first-order-logic.tex`; `introduction/`; `syntax-and-semantics/`; `models-theories/`; `proof-systems/`; `sequent-calculus/`; `natural-deduction/`; `tableaux/`; `axiomatic-deduction/`; `completeness/`; `beyond/` | Initial API: semantic consequence, monotonicity, unsatisfiable-negation equivalence, and semantic deduction theorem |
| `FormalOLP.ModelTheory` | `OpenLogic/content/model-theory/model-theory.tex`; `basics/`; `models-of-arithmetic/`; `interpolation/`; `lindstrom/` | Scaffold |
| `FormalOLP.Computability` | `OpenLogic/content/computability/computability.tex`; `recursive-functions/`; `computability-theory/` | Supporting API: staged oracle/Turing reducibility model; OLP machine/many-one equivalence pending |
| `FormalOLP.TuringMachines` | `OpenLogic/content/turing-machines/turing-machines.tex`; `machines-computations/`; `undecidability/` | Scaffold |
| `FormalOLP.Incompleteness` | `OpenLogic/content/incompleteness/incompleteness.tex`; `introduction/`; `arithmetization-syntax/`; `representability-in-q/`; `theories-computability/`; `incompleteness-provability/` | Scaffold |
| `FormalOLP.SecondOrderLogic` | `OpenLogic/content/second-order-logic/second-order-logic.tex`; `syntax-and-semantics/`; `metatheory/`; `sol-and-set-theory/` | Scaffold |
| `FormalOLP.LambdaCalculus` | `OpenLogic/content/lambda-calculus/lambda-calculus.tex`; `introduction/`; `syntax/`; `church-rosser/`; `lambda-definability/` | Scaffold |
| `FormalOLP.ManyValuedLogic` | `OpenLogic/content/many-valued-logic/many-valued-logic.tex`; `syntax-and-semantics/`; `three-valued-logics/`; `infinite-valued-logics/`; `sequent-calculus/` | Scaffold |
| `FormalOLP.NormalModalLogic` | `OpenLogic/content/normal-modal-logic/normal-modal-logic.tex`; `syntax-and-semantics/`; `frame-definability/`; `axioms-systems/`; `completeness/`; `filtrations/`; `tableaux/`; `sequent-calculus/` | Initial API: native K/T/D/4 semantics, soundness, and frame correspondences |
| `FormalOLP.AppliedModalLogic` | `OpenLogic/content/applied-modal-logic/applied-modal-logic.tex`; `epistemic-logic/`; `temporal-logic/` | Scaffold |
| `FormalOLP.IntuitionisticLogic` | `OpenLogic/content/intuitionistic-logic/intuitionistic-logic.tex`; `introduction/`; `semantics/`; `soundness-completeness/`; `tableaux/` | Initial API: native Kripke semantics and basic soundness chain |
| `FormalOLP.Counterfactuals` | `OpenLogic/content/counterfactuals/counterfactuals.tex`; `introduction/`; `minimal-change-semantics/` | Scaffold |
| `FormalOLP.SetTheory` | `OpenLogic/content/set-theory/set-theory.tex`; `story/`; `z/`; `ordinals/`; `spine/`; `replacement/`; `ord-arithmetic/`; `cardinals/`; `card-arithmetic/`; `choice/` | Initial API: membership language, extensionality, empty-set and pairing uniqueness |
| `FormalOLP.Methods` | `OpenLogic/content/methods/methods.tex`; `proofs/`; `induction/` | Scaffold |
| `FormalOLP.ProofTheory` | `OpenLogic/content/proof-theory/proof-theory.tex`; `sequent-calculus/`; `cut-elimination/`; `natural-deduction/`; `normalization/`; `propositions-as-types/`; `proof-search/` | Scaffold |
| documentation only (no Lean module) | `OpenLogic/content/history/history.tex`; `biographies/`; `set-theory/` | Editorial and historical context; retained for source mapping |
| documentation only (no Lean module) | `OpenLogic/content/reference/reference.tex`; `greek-alphabet/`; `fraktur-alphabet/` | Reference and notation material; retained for source mapping |

## Status and dependency boundary

The root `FormalOLP.lean` imports the mathematical topic aggregators so the
module tree is visible to the build.  History and Reference remain mapped as
documentation-only source parts and have no empty Lean modules.  The native
scaffold has no Lean Pool dependency.  The initial set result uses Mathlib's
`Set` lattice and
does not assert that any textbook syntax, valuation, proof calculus, or model
is definitionally the same as a future imported development.

The current initial APIs include the absorption proposition from
`OpenLogic/content/sets-functions-relations/sets/proofs-about-sets.tex`:

```lean
FormalOLP.SetsFunctionsRelations.intersection_union_absorption
```

and the native function chain in
`FormalOLP.SetsFunctionsRelations.Functions`:

```lean
FormalOLP.SetsFunctionsRelations.composition_mapsTo
FormalOLP.SetsFunctionsRelations.composition_injOn
FormalOLP.SetsFunctionsRelations.composition_surjOn
FormalOLP.SetsFunctionsRelations.composition_bijOn
FormalOLP.SetsFunctionsRelations.leftInverse_injOn
FormalOLP.SetsFunctionsRelations.rightInverse_surjOn
FormalOLP.SetsFunctionsRelations.inverse_bijOn
```

and the semantic-notions chain from
`OpenLogic/content/first-order-logic/syntax-and-semantics/semantic-notions.tex`:

```lean
FormalOLP.FirstOrderLogic.SemanticNotions.semantic_consequence_of_mem
FormalOLP.FirstOrderLogic.SemanticNotions.semantic_consequence_mono
FormalOLP.FirstOrderLogic.SemanticNotions.semantic_consequence_iff_unsatisfiable_negation
FormalOLP.FirstOrderLogic.SemanticNotions.semantic_deduction_theorem
```

These declarations use Mathlib's `FirstOrder.Language` syntax and semantics
through a small FormalOLP namespace wrapper.  They do not assert a bridge to a
proof system or to completeness; those interfaces remain future work.

The source text is not copied into Lean files.  This map is source attribution
and planning metadata only.

The initial SetTheory API in `FormalOLP.SetTheory.Basic` defines a native
membership language and its atomic realization theorem, then ports the
model-level consequences of Extensionality and Pairing from the FoZfc source:
`ModelExtensionality.emptyset_exists_unique`, `pair_exists_unique`, and
`singleton_exists_unique`, with separate uniqueness lemmas.  The model
structure carries `Nonempty V`, matching the nonempty-model convention used
by the first-order semantic API.  The API does not claim a full ZF or ZFC
model.

The computability API currently exposes a supporting Turing-reducibility chain:

```lean
FormalOLP.Computability.turingReducible
FormalOLP.Computability.turingReducible_refl
FormalOLP.Computability.turingReducible_trans
FormalOLP.Computability.turingEquivalent
FormalOLP.Computability.turingEquivalent_equivalence
FormalOLP.Computability.setTuringReducible
FormalOLP.Computability.setTuringEquivalent_equivalence
```

These declarations use a native `RecursiveIn` oracle model adapted from the
Lean Pool `Computability/Oracle.lean` and `Computability/TuringDegree.lean`
declarations; the public declarations live entirely under
`FormalOLP.Computability` and no longer import the Lean Pool library.  The OLP
chapter's worked reductions are many-one, while its Turing-reduction paragraph
is a digression.  No equivalence to the OLP machine or many-one definitions
has been proved yet, so this chain is supporting semantics rather than a
completed OLP theorem integration.

## Pool source attribution

The temporary Lean Pool source staging was removed after the applicable
mathematics was integrated into native modules. The exact pinned revision,
source declaration families, and historical per-file manifest are documented
in [`docs/lean-pool-provenance.md`](lean-pool-provenance.md) and
[`docs/lean-pool-integration.md`](lean-pool-integration.md). The archived
manifest is a historical record and is not a current source tree.

## Open Logic Project attribution

The Open Logic Text source is copyright the Open Logic Project and is licensed
under the [Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/).
The repository's source and license are at
[`OpenLogic/README.md`](../OpenLogic/README.md) and
[`OpenLogic/LICENSE.md`](../OpenLogic/LICENSE.md).  When FormalOLP distributes
adapted textbook material, it must preserve that attribution, identify changes,
and link to the license.  This CC BY 4.0 attribution is intentionally separate
from the licenses and provenance records for any future Lean source; the
native topic modules contain no copied Pool declarations. Historical Pool
source records and notices are linked from the provenance ledger.
