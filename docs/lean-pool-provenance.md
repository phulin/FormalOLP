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
| `propositional-logic/syntax-and-semantics/valuations-sat.tex`: recursive valuations and semantic entailment | None; native definitions over the shared `FormalOLP.PropositionalLogic.Formula` | `Evaluate`, `SatisfiesContext`, `Entails`, `entails_of_mem`, `entails_mono`, `entails_modus_ponens`, `entails_deduction` | Newly authored native OLP semantics; checked. Full completeness and compactness remain pending. |
| `proof-theory/natural-deduction/rules-N2.tex`: propositional N2c derivations and soundness | None; native derivation tree and classical valuation semantics | `FormalOLP.ProofTheory.Derivation`, weakening, `finite_support`, `soundness`, `theorem_soundness` | Newly authored native OLP proof theory; checked. Quantifier and normalization metatheory remain pending. |
| `intuitionistic-logic/soundness-completeness/soundness-nd.tex`: intuitionistic natural-deduction soundness | None for the derivation object; earlier semantic lemmas are Pool-guided above | `IntuitionisticDerivation`, `toDerivation`, `derivation_sound`, `proof_sound` | Newly authored native OLP chain; checked. Completeness remains pending. |
| `normal-modal-logic/frame-definability/properties-accessibility.tex`: B and 5 frame correspondences | Historical Pool modal semantics used as guidance; correspondence proofs are native | `frame_valid_axiomB_iff_symmetric`, `frame_valid_axiomFive_iff_euclidean` | Native theorem extension; checked. Hilbert completeness remains pending. |
| `applied-modal-logic/epistemic-logic/epistemic-logic.tex`: multi-agent knowledge and common knowledge | None; native relational semantics | `satisfies_axiomK`, `satisfies_factivity`, `satisfies_positive_introspection`, `satisfies_negative_introspection`, `Reach`, `CommonKnowledge`, `commonKnowledge_iff_fixedPoint` | Newly authored native OLP chain; checked. Temporal logic and announcement dynamics remain pending. |
| `counterfactuals/minimal-change-semantics/sphere-models.tex`: closest-world conditional principles | None; explicit set-valued closest-world selection with limit and strong-centering hypotheses | `conditional_identity`, `conditional_vacuous`, `conditional_consequent_conjunction`, `conditional_modus_ponens_of_centering`, `antecedent_extensionality` | Newly authored selected variant; checked. It does not impose singleton selection, claim Stalnaker semantics, or claim the full sphere-model theorem family. |
| `second-order-logic/syntax-and-semantics/satisfaction.tex`: typed relation-variable full semantics | None; native typed relational fragment | `Satisfies`, `satisfies_rel_agreement`, `allRel_elim`, `allRel_intro`, `allRel_intro_of_not_free` | Newly authored native OLP chain; checked. Function variables and metatheory remain pending. |
| `turing-machines/machines-computations/turing-machines.tex`: deterministic machine operations and finite computations | Mathlib `Computability.TuringMachine.PostTuringMachine` tape primitives | `Machine`, `Configuration`, `step`, `run`, `Computation`, `Reaches`, and determinism/transitivity lemmas | Newly authored Mathlib-backed wrapper; checked. No bridge to `RecursiveIn` is claimed. |
| `representability-in-q/representability-in-q.tex`: Robinson arithmetic language, Q axioms, and standard model | Mathlib first-order syntax and realization | `QLanguage`, `qAxiom₁`–`qAxiom₇`, `standardNat_qAxiom₁`–`₇`, `standardNatModel`, `robinsonQ_isSatisfiable` | Newly authored Mathlib-backed OLP chain; checked. Representability and incompleteness remain pending. |
| `model-theory/basics/basics.tex`: isomorphism, elementary equivalence, and compactness bridges | Mathlib first-order isomorphism and compactness APIs | `isomorphism_preserves_sentence`, `isomorphic_implies_elementarilyEquivalent`, theory preservation, `compactness`, `compactness_of_finite_satisfiability` | Newly authored Mathlib-backed OLP chain; checked. Interpolation and Lindström results remain pending. |
| `methods/induction/induction-on-N.tex`, `strong-induction.tex`, and `relations.tex`: reusable induction principles | Mathlib natural-number and well-founded induction APIs | `weak_induction`, `strong_induction`, `wellFounded_induction`, `measure_induction`, `weak_induction_succ` | Newly authored native OLP methods chain; checked. The broader methods chapter remains pending. |
| `many-valued-logic/three-valued-logics/kleene.tex`: strong Kleene K3 truth values and designated semantics | None; native finite truth tables over the shared formula syntax | `K3`, `evaluate`, `designated`, `entails`, `reflection`, `modus_ponens_designated`, `k3_valid_implies_classical_valid`, `excluded_middle_not_valid` | Newly authored native OLP chain; fresh warning-as-error check passes. Other many-valued systems remain pending. |
| `lambda-calculus/syntax/de-bruijn.tex`, `substitution.tex`, and `beta.tex`: scoped syntax, capture-avoiding substitution, and contextual beta reduction | None; indexed native representation | `Term`, `rename`, `rename_composition`, `subst`, `subst_rename`, `rename_subst`, `subst_composition`, `BetaStep`, `BetaStar`, and scope-preservation theorems | Newly authored native OLP chain; fresh warning-as-error check passes. Named syntax, Church--Rosser, normalization, and lambda definability remain pending. |

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
