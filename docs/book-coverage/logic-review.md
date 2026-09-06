# Logic book coverage review

This review audits the ten requested Open Logic source areas against the
active native declarations under `FormalOLP/`.  The source checkout is the
initialized `OpenLogic` submodule at commit
`1e960beff9ed7835bf3e3f1335e21af3439cd107`.  The source roots are:

- `OpenLogic/content/propositional-logic`
- `OpenLogic/content/first-order-logic`
- `OpenLogic/content/proof-theory`
- `OpenLogic/content/model-theory`
- `OpenLogic/content/intuitionistic-logic`
- `OpenLogic/content/normal-modal-logic`
- `OpenLogic/content/applied-modal-logic`
- `OpenLogic/content/counterfactuals`
- `OpenLogic/content/second-order-logic`
- `OpenLogic/content/many-valued-logic`

The companion [logic.tsv](logic.tsv) uses the canonical 24-column
`foundations.tsv` schema: the 19-column source inventory core, followed by
coverage status, basis, evidence, declarations, and audit note.  It has one
section row for every source `.tex` file, one unit row for every recognized
`defn`, `thm`, `prop`, `lem`, `cor`, `prob`, `ex`, `example`, or `exercise`,
and additional declaration rows for native chains that cross a mixed source
section.  It has 1,393 data rows: 388 source-section rows, 985 source-unit
rows, and 20 explicit native declaration rows.  Each source-unit row retains
its ordinal, optional OLP label, title, and source line interval.  Each section
inventory retains all recognized environment counts, all `\ollabel` values,
and all environment titles.  Thus an unlabelled definition, theorem,
exercise, or example is still accounted for.  The source paths in the TSV are
relative to `OpenLogic/content`; `formalolp_evidence` identifies the native
file and `formal_declarations`/`audit_note` preserve the exact native line
reference and boundary.

The source corpus contains 556 `\ollabel` values and 985 recognized formal
environments.  Of those environments, 236 are `prob` exercises and 95 are
`ex` exercises (no `example` or `exercise` environment occurs in these ten
roots).  The per-root denominator is:

| Source root | `.tex` files | Formal units | `prob` | `ex` | Exercise/example units |
| --- | ---: | ---: | ---: | ---: | ---: |
| `propositional-logic` | 10 | 41 | 11 | 1 | 12 |
| `first-order-logic` | 123 | 371 | 92 | 51 | 143 |
| `proof-theory` | 59 | 94 | 22 | 5 | 27 |
| `model-theory` | 27 | 84 | 17 | 3 | 20 |
| `intuitionistic-logic` | 26 | 54 | 14 | 6 | 20 |
| `normal-modal-logic` | 69 | 201 | 46 | 18 | 64 |
| `applied-modal-logic` | 16 | 19 | 1 | 0 | 1 |
| `counterfactuals` | 13 | 11 | 6 | 3 | 9 |
| `second-order-logic` | 20 | 46 | 5 | 5 | 10 |
| `many-valued-logic` | 25 | 64 | 22 | 3 | 25 |
| **Total** | **388** | **985** | **236** | **95** | **331** |

The audit traversed every file and records all source units even when a file
has no active Lean target.  Coverage status was assigned by explicit source
path and source-unit mappings for the sections touched by the native API;
remaining substantive units are conservatively `missing`, rather than being
credited from a topic import or a similarly named declaration.  The inventory
is exhaustive, but the semantic review is not a line-by-line proof of absence
for every unmapped unit: unmapped rows mean that no native correspondence was
found in this audit and require future review before being called formally
confirmed missing.  Rows with `source_unit=section` and `coverage_status=structural_container` are
part/chapter aggregators or editorial import containers with no formal units.
The single `dependency_only` section is the first-order compactness source,
where the active result is imported from Mathlib and is therefore
`dependency_only`, not native source coverage.  The source-section summary is (structural containers remain in the denominator but are not formal coverage):

| Source root | Sections | structural_container | dependency_only | proved_equivalent | proved_weaker | defined_only | missing |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `propositional-logic` | 10 | 2 | 0 | 0 | 3 | 1 | 4 |
| `first-order-logic` | 123 | 13 | 1 | 0 | 1 | 0 | 108 |
| `proof-theory` | 59 | 7 | 0 | 0 | 2 | 0 | 50 |
| `model-theory` | 27 | 5 | 0 | 0 | 1 | 0 | 21 |
| `intuitionistic-logic` | 26 | 5 | 0 | 0 | 3 | 1 | 17 |
| `normal-modal-logic` | 69 | 8 | 0 | 0 | 5 | 2 | 54 |
| `applied-modal-logic` | 16 | 3 | 0 | 1 | 1 | 2 | 9 |
| `counterfactuals` | 13 | 3 | 0 | 0 | 2 | 0 | 8 |
| `second-order-logic` | 20 | 4 | 0 | 0 | 2 | 1 | 13 |
| `many-valued-logic` | 25 | 5 | 0 | 0 | 3 | 0 | 17 |
| **Total** | **388** | **55** | **1** | **1** | **23** | **7** | **301** |

The four initially `proved_equivalent` section candidates were checked against their full source files.  The intuitionistic relational-model and soundness sections include source exercises, and the modal accessibility section includes an additional five-row table and counterexample material; they are therefore recorded as `proved_weaker`.  The applied epistemic accessibility section has no separate theorem/exercise environments and its four source table principles are all represented, so it remains the one `proved_equivalent` section row.

The statuses have narrow meanings:

- `proved_equivalent` means the referenced native declaration has the same
  mathematical statement and explicit hypotheses as the mapped source unit
  at the stated level of generality.
- `proved_weaker` means a genuine fragment or restricted representation is
  proved, while source results, examples, connectives, or hypotheses remain
  outside it.
- `defined_only` means a native object or interface corresponds to the
  source definition, without claiming the surrounding source theorem chain.
- `structural_container` identifies an aggregator/editorial import container
  with no formal source unit.
- `dependency_only` identifies an external support result; it is not source
  theorem coverage.
- `missing` is the audit shorthand for no-native-match-found/unverified: no active native declaration was found during this pass.  It is not a claim that a future search or implementation cannot cover the unit.

A section row can be `proved_weaker` while its individual source-unit rows
are `missing`; the latter is intentional when a native fragment does not
prove the named source result.  The extra declaration rows identify the
fragment that justified the section-level status.

## Native chains found

The native declarations and their source boundaries are as follows.

- **Propositional logic.** `FormalOLP.PropositionalLogic.Syntax.Formula`,
  `neg`, and `verum` are in
  `FormalOLP/PropositionalLogic/Syntax.lean:20-45`.  The valuation,
  recursive evaluation, satisfaction, context satisfaction, satisfiability,
  tautology, entailment, monotonicity, modus ponens, and semantic deduction
  API is in `FormalOLP/PropositionalLogic/Semantics.lean:24-129`.
  `valuations-sat.tex` therefore has definition-level coverage and a
  partial semantic fragment; its Local Determination theorem, satisfaction
  versus truth-value proposition, formation-sequence development, and
  exercises remain missing.  The source soundness row is only proved_weaker because
  `FormalOLP.ProofTheory.Derivation.soundness` uses native N2c derivations,
  not the source axiomatic calculus.

- **First-order logic.**
  `FormalOLP.FirstOrderLogic.SemanticNotions` provides sentence/theory
  semantic consequence, membership consequence, monotonicity,
  unsatisfiable-negation, and the sentence-level deduction theorem in
  `FormalOLP/FirstOrderLogic/SemanticNotions.lean:35-78`.  It uses Mathlib's
  first-order syntax and nonempty-model semantics.  It does not cover the
  source term/formula syntax, quantifier semantics, proof systems, or
  completeness development.  The compactness source section is recorded as
  `dependency_only` where the active theorem is imported from
  `FormalOLP/ModelTheory/Basic.lean:52-60`, not proved as a native OLP
  completeness result.

- **Proof theory.**  `FormalOLP.ProofTheory.NaturalDeduction.Derivation` in
  `FormalOLP/ProofTheory/NaturalDeduction.lean:31-301` is a native
  propositional N2c proof object with weakening, finite support, and
  soundness.  The source N2 natural-deduction rule section and proof section
  are proved_weaker because quantifier rules, the source presentation, and
  the rest of the proof-theory chapters are absent.  Cut elimination,
  normalization, sequent calculus, proof search, and propositions-as-types
  source units are missing.

- **Model theory.**  `FormalOLP.ModelTheory.Basic` defines isomorphism and
  elementary-equivalence aliases over Mathlib and proves sentence and theory
  preservation in `FormalOLP/ModelTheory/Basic.lean:23-50`.  The source
  assignment-level five-clause isomorphism proof and its exercises are not
  re-declared.  Compactness at lines 52-60 is a Mathlib support boundary;
  interpolation, Lindström, and models-of-arithmetic sections are missing.

- **Intuitionistic logic.**  `FormalOLP.IntuitionisticLogic.Kripke` defines
  nonempty partial-order frames, persistent valuations, forcing, and
  `forces_hereditary` in `FormalOLP/IntuitionisticLogic/Kripke.lean:28-101`.
  `FormalOLP.IntuitionisticLogic.NaturalDeduction` defines the standalone
  Type-valued intuitionistic derivation tree and proves `derivation_sound`
  and `proof_sound` in `FormalOLP/IntuitionisticLogic/NaturalDeduction.lean:36-196`.
  These support proved_weaker section rows and two proved source-unit mappings, with explicit limits:
  no completeness, BHK formalization, tableaux, or source exercises are
  claimed, and the intuitionistic tree has no classical RAA constructor.

- **Normal modal logic.**  `FormalOLP.NormalModalLogic.Syntax` and
  `Semantics` provide the native language, nonempty relational models, truth,
  and validity interfaces.  `FormalOLP.NormalModalLogic.Soundness.lean:32-249`
  proves the K/T/D/4/B/5 schema and frame-property correspondence chains.
  The source accessibility theorem is credited only for the first five
  explicit correspondence directions; the section remains proved_weaker because
  its exercises, counterexample proposition, and additional five-row table
  are not native.  Modal completeness, filtration, tableaux,
  sequent calculus, and the additional axiom-system chapters remain missing.

- **Applied modal logic.**
  `FormalOLP.AppliedModalLogic.Epistemic` defines multi-agent epistemic
  formulas, agent-indexed frames and models, truth, K, factivity/T, positive
  introspection/4, negative introspection/5, reachability, and a semantic
  common-knowledge fixed-point law in
  `FormalOLP/AppliedModalLogic/Epistemic.lean:19-199`.  Relation properties
  are explicit per agent.  The four source table principles are represented
  by the native K/factivity/positive-introspection/negative-introspection
  declarations.  Common knowledge is represented semantically and has no
  formula constructor; public announcement, bisimulation, and all
  temporal-logic source directories are missing.

- **Counterfactuals.**  `FormalOLP.Counterfactuals.Sphere` uses a selected
  closest-world model with explicit success/limit and strong-centering
  conditions.  It proves identity, vacuity, consequent conjunction,
  centered modus ponens, and antecedent extensionality in
  `FormalOLP/Counterfactuals/Sphere.lean:23-137`.  This is a
  `proved_weaker` Stalnaker-style selection fragment, not the source's
  general Lewis sphere systems: the source permits nested sphere systems
  without an innermost antecedent sphere.  No source figure or counterexample
  is counted as a theorem.

- **Second-order logic.**  `FormalOLP.SecondOrderLogic.Semantics` provides
  typed relation-variable formulas, object assignments, full relation
  quantification, satisfaction, free-variable agreement, and fresh
  relation-quantifier introduction/elimination in
  `FormalOLP/SecondOrderLogic/Semantics.lean:22-196`.  The source's function
  variables, term language, full term evaluation, metatheory, and set-theory
  applications remain missing, so the satisfaction and semantic-notions
  sections are proved_weaker.

- **Many-valued logic.**  `FormalOLP.ManyValuedLogic.Kleene` defines the
  three K3 values, strong K3 truth tables, designated semantics, reflection,
  modus ponens, classical-validity reflection, and excluded-middle
  non-validity in `FormalOLP/ManyValuedLogic/Kleene.lean:19-235`.  The source
  section develops both strong and weak Kleene logics and a broader discussion;
  only the strong K3 fragment is native.  Bochvar, Łukasiewicz, LP, Gödel,
  infinite-valued, and many-valued sequent-calculus units are missing.

## Gaps and interpretation boundaries

The dominant gap is theorem-chain coverage, not an absent aggregator import.
First-order logic has 108 missing source sections in the section denominator,
including most syntax, proof-system, natural-deduction, tableau, axiomatic,
and completeness material.  Proof theory has 50 missing sections, including
cut elimination, normalization, sequent calculus, proof search, and
propositions-as-types.  Normal modal logic has 54 missing sections, including
completeness and filtration.  Applied modal logic's native epistemic chain
leaves public-announcement, bisimulation, and temporal logic missing.
Second-order logic's relation-only API does not imply source coverage of
function variables or full second-order metatheory.  The counterfactual model
variant does not imply the Lewis sphere chapter, and K3 does not imply the
other many-valued systems.

The file and unit rows include every counted exercise and example so that
unproved pedagogical material cannot disappear into an aggregate status.  The
55 structural_container rows are retained in the denominator but are not
mathematical source sections.  A
`prob` or `ex` row is `missing` unless a specific native declaration and
hypothesis boundary are recorded.  Source labels alone never create a native
correspondence.  Likewise, a Mathlib theorem is marked `dependency_only` or
`proved_weaker` when its API is supporting a FormalOLP definition rather
than reproducing the source proof.

This is a coverage audit of the current scaffold and native chains.  It does
not claim that the Open Logic book has been formalized, nor that the remaining
source rows are interchangeable with similarly named Lean modules.  The
`missing` rows are review leads for the next pass, not independently verified
negative theorems.
