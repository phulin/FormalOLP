# Native integration provenance

This ledger covers the current FormalOLP tree after the temporary Lean Pool
source staging was retired. Native modules do not import a `LeanPool` library.
The historical vendor inventory, immutable Pool revision, per-file hashes,
and compatibility edits are archived in
[`archive/lean-pool-vendor-manifest.tsv`](archive/lean-pool-vendor-manifest.tsv)
and the dated archive documents. Those files are historical records; their
paths are not claimed to exist in the current tree.

The source reference used for mathematical comparison is Lean Pool commit
[`c8ddda0a64f21cb019720cdda48c94354d4091e7`](https://github.com/Vilin97/lean-pool/tree/c8ddda0a64f21cb019720cdda48c94354d4091e7).
The archival vendor state is recorded by commits `13018b2` and `157ec9f`.
Current native file hashes and source paths are checked by
[`native-integration-manifest.tsv`](native-integration-manifest.tsv) and
[`check-native-integration.sh`](../scripts/check-native-integration.sh).

## Native declaration ledger

An integration unit is an OLP source statement, native FormalOLP definitions,
and a checked proof. A source theorem with a similar name is proof guidance;
it is not imported or silently counted as an OLP theorem.

| OLP source and statement | Pool source used as mathematical guidance | Native declarations | Status |
| --- | --- | --- | --- |
| `sets-functions-relations/functions/function-kinds.tex`, `composition.tex`: maps between explicit domains/codomains preserve composition, injectivity, surjectivity, and bijectivity | `ZFSet.IsFunc_of_composition_IsFunc`, `ZFSet.IsInjective.composition_of_injective`, `ZFSet.IsSurjective.composition_of_surjective`, `ZFSet.IsBijective.composition_of_bijective` in `ZFLean/Functions.lean` | `FormalOLP.SetsFunctionsRelations.composition_mapsTo`, `composition_injOn`, `composition_surjOn`, `composition_bijOn` | Adapted native Mathlib `Set` proofs; checked. |
| `sets-functions-relations/functions/inverses.tex`: left/right inverse consequences and two-sided inverse bijection | `ZFSet.inv_is_func_of_injective`, `ZFSet.inv_is_func_of_bijective`, `ZFSet.inv_bijective_of_bijective` in `ZFLean/Functions.lean` | `leftInverse_injOn`, `rightInverse_surjOn`, `inverse_bijOn` in `FormalOLP.SetsFunctionsRelations.Functions` | Adapted native Mathlib `Set` proofs; `MapsTo` hypotheses preserve both textbook codomains; checked. |
| `intuitionistic-logic/semantics/relational-models.tex`, `defn:true-at-w`, `prop:true-monotonic`: forcing over a nonempty partial-order frame is persistent | `LO.IntProp.Kripke.Frame`, `Valuation`, `Model`, `Formula.Kripke.Satisfies` in `Incompleteness/Foundation/IntProp/Kripke/Basic.lean` | `FormalOLP.IntuitionisticLogic.Frame`, `Valuation`, `Model`, `Forces`, `forces_hereditary`, `Model.Valid`, `Frame.Valid` | Native semantic chain; checked. |
| `intuitionistic-logic/soundness-completeness/soundness-nd.tex`: semantic validity of the elementary axiom/rule instances used before natural deduction soundness | `LO.IntProp.Formula.Kripke.ValidOnModel.andElim₁`, `andElim₂`, `andInst₃`, `orInst₁`, `orInst₂`, `orElim`, `imply₁`, `imply₂`, `mdp`, `efq` and frame variants | `model_valid_axiomImply₁`, `model_valid_axiomImply₂`, `model_valid_axiomAndElimLeft/Right`, `model_valid_axiomAndIntro`, `model_valid_axiomOrIntroLeft/Right`, `model_valid_axiomEfq`, `model_valid_orElim`, `model_valid_mdp`, and frame lifts | Native semantic lemmas; checked. No derivation object and no claim of full natural-deduction soundness. |
| `set-theory/story/extensionality.tex`, `set-theory/z/pairs.tex`, and the ZFC axiom list in `set-theory/cardinals/milestone.tex`: membership language, extensionality, and model-level empty/pair consequences | `LZFC`, `ModelSets`, `ModelSets.extensionality`, `realize_in`, `ModelEmptyset`, `realize_is_emptyset`, `ext_emptyset_exists`, `ext_emptyset_unique`, `ModelPairing`, `realize_is_singleton`, `realize_is_pair`, `ext_pairing`, `ext_singleton_unique`, and `ext_pair_unique` in historical `FoZfc/Basic.lean` and `FoZfc/Axioms.lean` | `FormalOLP.SetTheory.Language`, `membershipFormula`, `Mem`, `realize_membership`, `Extensionality`, `ModelExtensionality`, `emptyset_unique`, `emptyset_exists_unique`, `pair_unique`, `pair_exists_unique`, `singleton_unique`, `singleton_exists_unique` | Native model-level consequences; checked. Nonempty carrier is explicit. Full ZF/ZFC axiom schemata and set existence are not claimed. |
| `normal-modal-logic` relational semantics and K/T/D/4 frame facts | Historical `LO.Modal.Formula`, `LO.Modal.Kripke.Frame`, `LO.Modal.Kripke.Model`, `LO.Modal.Formula.Kripke.Satisfies`, `LO.Axioms.K/T/D/Four`, `ValidOnModel.axiomK`, `ValidOnFrame.axiomK`, `ValidOnModel.nec`, `ValidOnFrame.nec`, `LO.Modal.Kripke.reflexive_of_validate_AxiomT`, and `transitive_of_validate_AxiomFour` declarations | `FormalOLP.NormalModalLogic` syntax, models, forcing, soundness, and frame correspondence declarations | Native theorem chain; checked. D correspondence is a new native proof because no matching generic Pool correspondence declaration was selected. |
| `computability/computability-theory/prop-reduce.tex` Turing-reduction digression | Historical Pool `Computability/Oracle.lean` and `TuringDegree.lean` `RecursiveIn`, `TuringReducible`, and `TuringEquivalent` declarations | `FormalOLP/Computability/RelativeComputability.lean` and `TuringReducibility.lean`: `RecursiveIn`, `turingReducible`, `turingEquivalent`, set adapters | Supporting oracle model; checked. Equivalence with OLP machine/many-one definitions remains pending. |

The current native source files carry declaration-level comments naming their
OLP paths and Pool guidance. Licensing is kept separate from theorem
provenance: the Open Logic Text attribution is recorded in `topic-map.md`,
while the preserved Lean Pool `LICENSE`, `NOTICE`, and `NOTICE.extra.yml`
remain under `third_party/lean-pool/` for the adapted-source reference. No
Lean Pool declaration is copied into the native modules.

## Pending bridges

The remaining retained source families have no native OLP bridge: FoZfc
replacement/model theory, Gödel incompleteness, bounded arithmetic, PCA
semantics, GL interpolation/fixed points, LTL/NBW model checking, and Lentil
temporal proof rules. Each next bridge must name a concrete OLP statement,
native representation, source declaration family, and checked proof before it
is added to this table.
