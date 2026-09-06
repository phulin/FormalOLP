# Foundations book-coverage review

This review audits the Open Logic Project source areas that are outside the
logic-worker chapters. The audited areas are `computability`, `history`,
`incompleteness`, `lambda-calculus`, `methods`, `reference`, `set-theory`,
`sets-functions-relations`, and `turing-machines`. The worker areas
`propositional-logic`, `first-order-logic`, `proof-theory`, `model-theory`,
`intuitionistic-logic`, `normal-modal-logic`, `applied-modal-logic`,
`counterfactuals`, `second-order-logic`, and `many-valued-logic` are excluded
from this file's partition.

The companion [foundations.tsv](foundations.tsv) contains one aggregate row for
each of the 332 TeX source sections and an additional row for every recognized
substantive `thm`, `prop`, `lem`, `cor`, `defn`, `example`, `exercise`, `prob`,
`claim`, `conj`, `remark`, `axiom`, `defish`, `derivation`, or `conv` unit. It therefore has 1,202 rows: 332 section
rows and 870 claim/definition/example rows. Every row records the exact source
file, the section heading, a source line interval, file size in lines and
words, the recognized units, the canonical `coverage_status`, and the active
Lean declarations when a correspondence exists. The core inventory columns
match `docs/book-coverage/inventory.tsv`; `source_unit` and line interval
columns extend that schema for theorem-level rows. Unlabelled units use their ordinal in the
source file; labelled units retain the OLP label.

The audit loaded the complete text of all 332 TeX files in the nine directories
and indexed their section headings, line ranges, labels, theorem-like
environments, and file word counts. The source corpus contains 1,263,406
bytes. `methods/methods.pcr` is an empty support file and contains no source
section. The TSV is an exhaustive source inventory and triage, not a claim
that every one of the 870 units was manually re-proved: path-specific source
classification was checked against the active Lean declaration inventory, and
the native foothold sections, all structural/non-formal sections, and the
proved_equivalent units were spot-checked against their actual source text
and hypotheses.
The aggregate section row records the complete file scope; mixed sections are
split again at every recognized theorem, definition, example, exercise, axiom,
or related unit so an unformalized result cannot disappear behind a broad
section label.

Coverage states have deliberately narrow meanings:

- `proved_equivalent` means the referenced native theorem has the same
  mathematical statement as the source unit at the stated level of
  generality.
- `proved_weaker` means a native chain covers a genuine fragment or a
  restricted representation, while source results, examples, or hypotheses
  remain outside it.
- `defined_only` means a source definition or listed statement
  has a corresponding native object/interface, without a source-equivalent
  proof chain being claimed.
- `dependency_only` is reserved for a source claim whose mathematics is
  supported by an explicitly recorded Lean dependency; no current row uses
  this state.
- `non_formal_exposition` means biography, narrative, notation, or teaching
  material with no mathematical declaration target.
- `structural_container` means a part/chapter/index file that only assembles
  source sections.
- `missing` means the source unit has no active native declaration recorded.

Exercises and examples are explicit rows when they use `prob`, `ex`, `example`,
or `exercise`; unlabelled units are retained by ordinal, and labelled units
retain their OLP label. Explanatory prose without a theorem-like environment
is represented by its aggregate section row rather than being mistaken for a
proved declaration. structural_container and non-formal exposition remain
visible in the inventory but are not counted as formal coverage.

The section-level counts are:

| Source area | TeX sections | dependency_only | non_formal_exposition | structural_container | proved_equivalent | proved_weaker | defined_only | missing |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `computability` | 44 | 0 | 0 | 3 | 0 | 1 | 0 | 40 |
| `history` | 20 | 0 | 12 | 3 | 0 | 0 | 0 | 5 |
| `incompleteness` | 50 | 0 | 0 | 6 | 0 | 1 | 0 | 43 |
| `lambda-calculus` | 44 | 0 | 0 | 5 | 0 | 5 | 0 | 34 |
| `methods` | 19 | 0 | 2 | 2 | 1 | 4 | 0 | 10 |
| `reference` | 3 | 0 | 2 | 1 | 0 | 0 | 0 | 0 |
| `set-theory` | 72 | 0 | 2 | 10 | 0 | 2 | 1 | 57 |
| `sets-functions-relations` | 58 | 0 | 0 | 9 | 0 | 3 | 0 | 46 |
| `turing-machines` | 22 | 0 | 0 | 3 | 0 | 4 | 0 | 15 |
| **Total** | **332** | **0** | **18** | **42** | **1** | **20** | **1** | **250** |

The claim-level rows are more conservative: they mark individual source
results as `missing` when only a nearby generic API exists. This is why the
aggregate partial counts must not be read as theorem-completion percentages.

## Active native chains

`FormalOLP.Methods.Induction` proves the ordinary successor induction,
strong induction, well-founded relation induction, and natural-valued measure
induction principles. The strong-induction section is the sole
`proved_equivalent` section-level match. The Absorption proposition is a
separate `proved_equivalent` unit inside the mixed
`methods/proofs/reading-proofs.tex` section; that section itself is
`proved_weaker` because it also contains teaching prose and an exercise. The ordinary induction section still
lacks the dice and finite-sum applications. The relations section lacks the
source's uniquely readable term, subterm, and depth developments. Structural
induction remains missing. The worked absorption proof in
`methods/proofs/reading-proofs.tex` matches
`FormalOLP.SetsFunctionsRelations.intersection_union_absorption`; the rest
of the proof-method chapters remain missing.

`FormalOLP.LambdaCalculus.DeBruijn` defines typed scoped de Bruijn terms,
renaming and lifted renaming, capture-avoiding lifted substitution, identity
and composition laws, raw erasure, well-scopedness, contextual beta steps,
reflexive-transitive beta reduction, and scope preservation. This is a
restricted representation chain. The OLP named-term syntax, free-variable
presentation, alpha-conversion interface, eta/conversion results,
Church--Rosser proof, normalization, and lambda-definability chapters are
not represented. In particular, the typed representation must not be counted
as an automatic named-term translation.

`FormalOLP.Computability.RelativeComputability` and
`FormalOLP.Computability.TuringReducibility` provide an oracle-recursion
inductive relation, its part-recursive inclusion, monotonicity and oracle
substitution, set many-one reductions, partial-function oracle reductions,
and reflexive/transitive/equivalence lemmas. The only source section mapped
directly is the small reducibility fragment. The source's primitive-recursive
function development, computably enumerable sets, coding, fixed points,
normal forms, Rice's theorem, complete sets, and halting proofs remain
missing.

`FormalOLP.TuringMachines.Basic` defines a finite-state, finite-alphabet
machine over Mathlib's tape, configurations, deterministic option-valued
steps, initial configurations, halted states, totalized runs, and finite
computations. It is a real machine API, but its state/tape representation is
narrower than the source's explicit string-configuration presentation. No
source-level machine-combination library, unary-number coding, universal
machine, verification chain, or undecidability theorem is present.

`FormalOLP.Incompleteness.RobinsonArithmetic` defines the Q language, Q
terms/bounded formulas, the seven Robinson-Q axioms, their membership proofs,
the standard natural-number model, and Q satisfiability. This is the initial
model fragment only. The source's arithmetization of symbols, terms, formulas,
and proofs; representability and beta-function machinery; provability
conditions; fixed-point, Lob, Tarski, Rosser, and first/second incompleteness
results are missing.

`FormalOLP.SetTheory.Basic` defines the membership-only first-order language,
model membership, extensionality, empty-set and pairing predicates, and
uniqueness lemmas. It does not formalize the source's ZF/ZFC axiom list,
ordinals, ordinal arithmetic, replacement, cardinals, cardinal arithmetic,
cumulative hierarchy, or choice. The milestone row is therefore
`defined_only`, not a claim that ZFC has been formalized.

`FormalOLP.SetsFunctionsRelations` proves one absorption identity for Mathlib
sets. `FormalOLP.SetsFunctionsRelations.Functions` proves maps-to,
injective/surjective/bijective composition, left/right-inverse implications,
and a set-level inverse bridge. These are honest set-level fragments. The
source's complete set operations, relation algebra and orders, graph
development, cardinality/enumerability proofs, infinity, Dedekind arguments,
and arithmetization are missing; the source's choice-based inverse existence
is not silently inferred from the right-inverse implication.

The leaf `history` biography pages and mythology, plus the two reference
alphabet pages, are `non_formal_exposition`: they are narrative or
notation-reference material without mathematical declaration targets. The
reference root and history/biography root are `structural_container`. The
history/set-theory appendix is
treated separately: its Cantor, Hilbert-curve, infinitesimal, limit, and
pathology material is substantive and appears as `missing` rows. Import-only
part/chapter files are `structural_container`. These files are all listed so
the audit does not silently omit source directories.

## Review conclusions and concrete gaps

The largest coverage gap is not a missing import. It is the unformalized
mathematical chain after each native foothold. Examples recorded explicitly in
the TSV include:

- `computability/computability-theory/halting-problem.tex`: both source
  diagonal/totalization proofs are `missing`; no halting undecidability
  theorem is present in the active computability API.
- `incompleteness/incompleteness-provability/first-incompleteness-thm.tex`:
  the source theorem is `missing`; the native Q satisfiability model does not
  provide coding, representability, or provability predicates.
- `lambda-calculus/church-rosser/*`: all source confluence and uniqueness
  results are `missing`; `BetaStar` only supplies the reduction relation and
  its scope-preservation theorem.
- `set-theory/ordinals/*`, `set-theory/replacement/*`, and
  `set-theory/choice/*`: source definitions and results are `missing`; the
  membership-model fragment does not provide transfinite recursion or choice.
- `sets-functions-relations/size-of-sets/*`: all cardinality and
  enumerability units are `missing`; the native composition/inverse API does
  not imply them.
- `turing-machines/undecidability/*`: all source undecidability units are
  `missing`; a finite run API is not a universal-machine or halting proof.

The TSV is the review boundary for this wave. Any later theorem integration
should change a row only with a checked active declaration reference and a
new caveat when the native representation has weaker hypotheses or a
restricted domain.
