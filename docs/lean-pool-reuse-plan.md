# Lean Pool reuse plan for FormalOLP

Status: exploration report and implementation plan

Date: 2026-09-05

Lean Pool snapshot inspected: `c8ddda0a64f21cb019720cdda48c94354d4091e7`

## Executive decision

FormalOLP should vendor selected, complete Lean Pool project closures into this
repository, preserve their existing `LeanPool/...` module paths and namespaces,
and put the Open Logic Project interface in small `FormalOLP/...` bridge modules.

The first import should be the entire `LeanPool.Incompleteness` closure: 183
modules and 54,610 lines. Despite its name, it contains first-order syntax and
semantics, proof calculi, soundness and completeness, compactness, intuitionistic
and modal logic, arithmetization, provability logic, and both incompleteness
theorems. Copying its complete closure maximizes reuse and avoids maintaining a
fragile hand-selected subset.

After that, vendor the directly relevant independent projects `FoZfc`, `ZFLean`,
`FormalizationOfBoundedArithmetic`, `PartialCombinatoryAlgebras`, and
`Computability`. Together with `Incompleteness`, this gives an initial reusable
corpus of 238 modules and approximately 74,288 lines.

Do not add Lean Pool as a moving Lake dependency yet. Its inspected snapshot is
on Lean `v4.34.0-rc1` and Mathlib `de5ce8a9...`, while FormalOLP is on Lean
`v4.34.0-rc2`, Mathlib `5fcc6656...`, and TauCeti `8525a756...`. A source vendor
followed by rebuilding against FormalOLP's one dependency graph makes any API
porting explicit and avoids competing transitive Mathlib pins.

## Goals and non-goals

The goal is the maximum amount of *useful* code reuse for formalizing the Open
Logic Project, while retaining textbook fidelity and a maintainable build.

This does not mean copying Lean Pool's entire roughly 1.4-million-line
collection. Most projects are unrelated to logic, and Lean Pool is intentionally
a collection of independent projects rather than one coherent API. Additional
projects should be imported only when an OLP chapter or an explicit bridge lemma
uses them.

Nor should an existing result be renamed and presented as an OLP theorem when
its hypotheses differ. In particular, Lean Pool's incompleteness results are
phrased using `R₀`, `IΣ₁`, `Sigma1Sound`, and `Delta1Definable`. FormalOLP must
prove explicit bridges to OLP's formulations involving Robinson arithmetic
`Q`, computable axiomatizability, consistency, and representability.

## Audited source inventory

### Directly relevant closures

| Lean Pool entry | Modules | Lines | Main OLP use |
|---|---:|---:|---|
| `LeanPool.Incompleteness` | 183 | 54,610 | FOL, modal/intuitionistic logic, arithmetization, incompleteness |
| `LeanPool.FoZfc` | 7 | 2,221 | ZF as a first-order theory and Replacement |
| `LeanPool.ZFLean` | 13 | 8,637 | Internal ZF sets, functions, naturals, integers, rationals |
| `LeanPool.FormalizationOfBoundedArithmetic` | 21 | 5,973 | Arithmetic models, formula complexity, bounded induction |
| `LeanPool.PartialCombinatoryAlgebras` | 7 | 1,293 | Combinators, fixed points, lambda-definability examples |
| `LeanPool.Computability` | 7 | 1,554 | Oracle computation, reducibility, jumps, arithmetic hierarchy |

These six projects are independent Lean Pool projects. The
`LeanPool.Incompleteness` closure does not import another Lean Pool project; it
imports only Mathlib modules and `Aesop`. All 182 files below
`LeanPool/Incompleteness/` are reachable from its entry module, so there are no
orphan files to omit.

### Optional later candidates

| Lean Pool entry | Modules | Lines | Possible use |
|---|---:|---:|---|
| `LeanPool.Lean4GlCoalgebras` | 18 | 12,510 | Provability/modal logic |
| `LeanPool.MatchingLogic` | 54 | 11,244 | Alternative completeness architecture |
| `LeanPool.SetTheory` | 9 | 3,290 | Advanced elementary embeddings/Kunen inconsistency |
| `LeanPool.PCFTheory` | 7 | 1,123 | Advanced set theory |
| `LeanPool.DomainTheory` | 149 | 50,187 | Semantics/domain theory |
| `LeanPool.LeanModelChecking` | 8 | 2,508 | Temporal/model-checking examples |
| `LeanPool.Lentil` | 44 | 5,560 | Formal-language infrastructure |
| `LeanPool.PumpingCfg` | 12 | 3,985 | Grammars and pumping results |
| `LeanPool.MRiscX` | 34 | 7,469 | Formal verification examples |
| `LeanPool.AFormalizationOfBorelDeterminacyInLean` | 39 | 10,223 | Trees, games, advanced set theory |

Importing every project in both tables would add approximately 182,387 lines,
but the second table should remain gated by concrete OLP uses. It contains large
specialized developments and creates more risk of collisions around generic
names such as `Language`, `Formula`, and `Model`.

## What `Incompleteness` gives us

### Foundation and first-order logic

The `Foundation/Logic` and `Foundation/FirstOrder` trees provide:

- languages, terms, formulas, binders, rewrites, and substitution;
- structures, valuation, satisfaction, theories, and semantic consequence;
- a one-sided sequent/Tait-style derivation system;
- soundness;
- completeness for encodable languages and general completeness;
- consistency/satisfiability equivalences;
- compactness, sublanguages, search trees, and ultraproducts;
- arithmetic languages, hierarchies, models, and representability machinery.

Representative APIs include:

```lean
FirstOrder.Completeness.completenessOfEncodable
FirstOrder.Completeness.complete
FirstOrder.Completeness.satisfiable_of_consistent
FirstOrder.Completeness.satisfiable_iff_consistent
FirstOrder.Completeness.consequence_iff_consequence
```

This should underpin the OLP first-order syntax, semantics, soundness,
completeness, compactness, and parts of model theory. OLP's exact natural
deduction, tableaux, and alternative sequent systems still require their own
derivation objects and translation/soundness lemmas.

### Modal logic

`Foundation/Modal` includes modal syntax and substitution, Hilbert systems,
Kripke frames and models, soundness, maximal consistent sets, canonical models,
truth lemmas, completeness, filtration, finite frames, frame correspondence,
and named systems including K, T, D, B, K4, S4, S5, GL, and Grz.

This is a strong match for OLP's normal-modal syntax and semantics, axiomatic
systems, completeness, filtrations, and frame-definability chapters. Modal
tableaux and the textbook's modal sequent calculi remain new work.

### Intuitionistic logic

`Foundation/IntProp` includes formula syntax, substitution, Hilbert systems,
Kripke frames/models, hereditary forcing, and soundness. It supports initial OLP
chapters on syntax, relational semantics, axiomatic derivation, and soundness.

It does not provide the full OLP intuitionistic completeness construction,
tableaux, BHK account, or topological semantics.

### Arithmetization and incompleteness

The arithmetic core supplies coding of syntax and derivations, definability
hierarchies, representability, substitution of numerals, diagonal and
multidiagonal lemmas, provability predicates, Hilbert-Bernays-Löb conditions,
Gödel and Rosser sentences, Löb's theorem, and first and second incompleteness.

The entry theorems have approximately these interfaces:

```lean
LeanPool.Incompleteness.goedelFirst
  (T : LO.FirstOrder.Theory ℒₒᵣ)
  [𝐑₀ wkn T]
  [LO.FirstOrder.Arith.Sigma1Sound T]
  [T.Delta1Definable] :
  ¬ LO.Entailment.Complete T

LeanPool.Incompleteness.goedelSecond
  (T : LO.FirstOrder.Theory ℒₒᵣ)
  [𝐈Sg1 wkn T]
  [T.Delta1Definable]
  [LO.Entailment.Consistent T] :
  T ⊬ ↑T.consistentₐ
```

The OLP bridge layer must state the textbook results first and then discharge
these hypotheses with separate, reusable lemmas. It must not silently identify
`R₀` with `Q` or `Delta1Definable` with OLP's exact computability condition.

## Other direct projects

### `FoZfc`

This uses Mathlib's `FirstOrder.Language` framework rather than the custom `LO`
framework. It defines a membership language and model classes for Empty Set,
Pairing, Union, Power Set, Infinity, Regularity, Comprehension, and
Replacement. It is useful for OLP's first-order presentation of set theory and
model-theoretic discussion.

Because it uses a different syntax framework, any connection to `LO.FirstOrder`
must be an explicit translation. The project does not supply OLP's full ordinal,
cardinal, Choice, cumulative-hierarchy, or rank developments.

### `ZFLean`

This is a concrete `ZFSet` development with relations, functions, embeddings,
isomorphisms, von Neumann naturals, integers, rationals, booleans, sums,
induction, and Cantor-Bernstein-style results. It is useful for OLP's elementary
sets/functions/relations material when the intended theorem is internal to ZF.

It should complement, not be conflated with, `FoZfc`: one is concrete internal
set construction, the other a first-order axiomatization.

### `Computability`

This provides relative partial computability, universal oracle evaluation,
Turing reducibility and degrees, joins, jumps, and the arithmetical hierarchy.
It is useful for advanced OLP computability material, but it does not replace the
textbook's concrete Turing machine syntax/configuration development or its
introductory primitive/general recursive functions.

### `PartialCombinatoryAlgebras`

This provides partial and total combinatory algebras, K/S combinators,
programming combinators, booleans, pairs, conditionals, fixed-point combinators,
a free algebra, and graph models. It is supporting infrastructure for lambda
definability, not a replacement for ordinary lambda terms, alpha equivalence,
capture-avoiding substitution, beta/eta reduction, or Church-Rosser.

### Bounded arithmetic

This supplies Mathlib-based arithmetic languages and semantics, displayed
variables, bounded formula classes, induction/order/model structures, and
algebraic properties of IOpen, IDelta0, and strengthened V0 models. It should be
used through explicit adapters for OLP's theories and models of arithmetic.

## Material Lean Pool does not currently cover

The audit found no dedicated usable development for these OLP subjects:

- OLP-style natural deduction and tableaux;
- general cut elimination, normalization, and proof search;
- ordinary untyped lambda calculus and Church-Rosser;
- concrete Turing machines and computations;
- many-valued logic;
- intuitionistic completeness and intuitionistic tableaux;
- modal tableaux and modal sequent calculus;
- epistemic and temporal logic;
- counterfactual logic;
- second-order logic;
- interpolation and Lindstrom's theorem;
- propositions-as-types;
- the full introductory ordinal/cardinal/Choice sequence.

These are future FormalOLP developments. Existing Lean Pool code can still
supply common finite-set, relation, syntax, or semantic infrastructure, but no
chapter should be marked covered on that basis alone.

## Repository and licensing design

### Proposed layout

```text
LeanPool/
  Incompleteness.lean
  Incompleteness/...
  FoZfc.lean
  FoZfc/...
  ZFLean.lean
  ZFLean/...
  Computability.lean
  Computability/...
  PartialCombinatoryAlgebras.lean
  PartialCombinatoryAlgebras/...
  FormalizationOfBoundedArithmetic.lean
  FormalizationOfBoundedArithmetic/...
FormalOLP/
  FirstOrder/...
  Modal/...
  Intuitionistic/...
  Incompleteness/...
  Computability/...
  SetTheory/...
docs/
  lean-pool-provenance.md
```

Add a dedicated `LeanPool` Lean library/glob in `lakefile.toml`. Preserve all
upstream internal imports and namespaces. `FormalOLP.lean` should import only
the FormalOLP-facing modules; it should not copy Lean Pool's generated global
index that imports every pooled project.

### License obligations

Lean Pool's root license is Apache-2.0, but `LeanPool/` is an aggregation whose
original authors retain copyright. The selected projects have these licenses:

- Apache-2.0: `Incompleteness`, `FoZfc`, `ZFLean`, and `SetTheory`;
- MIT: `FormalizationOfBoundedArithmetic` and
  `PartialCombinatoryAlgebras`;
- `Computability` is recorded by Lean Pool as Apache-2.0.

For every copied file:

1. Preserve the original copyright/author/license header.
2. Add a prominent modification notice when FormalOLP changes an Apache file.
3. Keep the Apache license and all relevant MIT copyright/permission notices.
4. Copy the applicable Lean Pool `NOTICE` attribution into a FormalOLP notice or
   provenance ledger.
5. Record the immutable Pool SHA, upstream URL, source SHA when known, copied
   paths, license, and local modifications.
6. Keep OpenLogic's CC BY 4.0 attribution separate from Lean source notices.

Some older Lean Pool metadata does not record exact original upstream SHAs.
Therefore the Lean Pool snapshot SHA is the authoritative source for the first
vendor operation. Upstream SHAs should be recorded only after file comparison,
never inferred from commit dates.

Known upstreams include:

- `FormalizedFormalLogic/Incompleteness`;
- `ishiut/fo_zfc`;
- `VTrelat/ZFLean`;
- `tannerduve/computability`;
- `andrejbauer/partial-combinatory-algebras`;
- `ruplet/formalization-of-bounded-arithmetic`.

Preserve Lean Pool's collision fixes rather than replacing files from their
older upstream repositories. Examples include the renamed set-theory notation
`∈ᶻ'` and project-specific namespace wrappers.

## Import workflow

For each project closure:

1. Fetch the immutable Lean Pool commit recorded above into a temporary staging
   checkout.
2. Compute the recursive `LeanPool.*` import closure from the desired entry
   module.
3. Confirm that every local import is present and list all external imports.
4. Copy the complete closure with paths and file headers unchanged.
5. Add or update `docs/lean-pool-provenance.md` with exact paths, hashes,
   licenses, and any modifications.
6. Commit the unmodified vendor snapshot separately from compatibility edits.
7. Port only what fails against FormalOLP's pinned Mathlib, recording each
   modified file.
8. Add small `FormalOLP` aliases and bridge lemmas only after the vendor closure
   builds cleanly.

Each update repeats this process from another immutable Pool SHA. Never vendor
from a moving branch without recording its resolved commit, and never overwrite
the tree from an original upstream without reconciling Lean Pool's adaptations.

## Verification gates

Every vendor wave should pass all of the following before its bridge work starts:

1. `lake build` for each selected Lean Pool entry module.
2. An aggregate import build containing TauCeti and all vendored entry modules.
3. The complete FormalOLP build.
4. Warning-as-error and standard Mathlib lint/style checks.
5. Scans rejecting `sorry`, `admit`, `unsafe`, `partial`, and `set_option`.
6. An axiom audit allowing only `Classical.choice`, `propext`, and `Quot.sound`.
7. Namespace and notation collision tests.
8. A provenance check ensuring every copied path has a license/commit entry.
9. A test that the OLP-facing theorem statement is the actual textbook claim,
   not merely an alias with different hypotheses.

Do not address slow declarations by increasing `maxHeartbeats`. Split or adapt
proofs according to this repository's Lean guidelines.

## Implementation waves

### Wave 1: governance and build scaffold

- Add `docs/lean-pool-provenance.md` with the snapshot and project ledger.
- Add a `LeanPool` library target/glob without changing the `FormalOLP` namespace.
- Add scripts or Lean executables for import-closure verification and axiom
  auditing.
- Add an aggregate compatibility module importing TauCeti plus vendored entries.
- Pin and document the one accepted Lean/Mathlib/TauCeti environment.

Expected copied mathematics: none. This wave makes later bulk copies auditable.

### Wave 2: complete `Incompleteness` closure

- Vendor all 183 modules / 54,610 lines at the pinned Pool snapshot.
- First commit the byte-for-byte vendor snapshot.
- In later commits, make only the compatibility changes required by FormalOLP's
  newer Mathlib pin.
- Build the exact `LeanPool.Incompleteness` entry, including its provability-logic
  import. Do not stop at the smaller 93-module/41,085-line arithmetic core,
  because the additional modal and intuitionistic infrastructure directly serves
  OLP chapters.
- Add initial OLP bridge modules for FOL syntax/semantics, soundness,
  completeness, modal semantics, and the two headline incompleteness results.

Expected cumulative copied mathematics: 54,610 lines.

### Wave 3: adjacent direct foundations

Vendor one complete project per commit, in this order:

1. `FoZfc` — 7 modules / 2,221 lines.
2. `Computability` — 7 modules / 1,554 lines.
3. `FormalizationOfBoundedArithmetic` — 21 modules / 5,973 lines.
4. `PartialCombinatoryAlgebras` — 7 modules / 1,293 lines.
5. `ZFLean` — 13 modules / 8,637 lines.

Add OLP bridges only after each project builds independently and in the aggregate.

Expected cumulative copied mathematics after three waves: approximately 74,288
lines in 238 modules.

### Wave 4: textbook-fidelity bridges

Build explicit reusable chains for:

- `Q` versus `R₀` and the exact theory-extension assumptions;
- computably axiomatized versus `Delta1Definable` theories;
- OLP consistency, completeness, and representability terminology;
- translations between Mathlib `FirstOrder.Language` and `LO.FirstOrder` where
  `FoZfc` results are needed by the `LO` development;
- concrete Turing computation versus partial/oracle computation;
- ordinary lambda calculus versus combinatory algebras.

Each bridge should be a sequence of small named lemmas, not a monolithic wrapper.

### Wave 5: conditional bulk imports

Evaluate the optional projects against concrete missing OLP declarations. Import
complete closures only when at least one OLP-facing theorem will depend on them.
Start with `Lean4GlCoalgebras`, `LeanModelChecking`, `PumpingCfg`, and `Lentil`;
defer `DomainTheory`, `MatchingLogic`, advanced `SetTheory`, and Borel determinacy
unless their large APIs clearly eliminate planned work.

## Suggested commit sequence

Use Conventional Commits-ish messages with explanatory bodies:

1. `docs: add Lean Pool provenance policy`
2. `build: add vendored Lean Pool library target`
3. `test: add vendored source verification gates`
4. `vendor: import Lean Pool incompleteness closure`
5. `fix: port Lean Pool incompleteness to pinned Mathlib`
6. `feat(first-order): expose OLP syntax and semantics bridges`
7. `feat(incompleteness): state OLP bridge theorems`
8. One `vendor:` commit per Wave 3 project, followed by separate compatibility
   and OLP-interface commits.

Vendor commit bodies should name the Lean Pool SHA, original upstream, license,
copied closure, and whether the files are byte-identical.

## Immediate next action on the new machine

Before copying any source:

1. Clone FormalOLP and initialize the `OpenLogic` submodule.
2. Confirm the repository's `lean-toolchain`, `lakefile.toml`, and manifest are
   committed or deliberately regenerated; at the time of this report they were
   present locally but untracked.
3. Configure the intended `upstream` remote. The coordinator instructions ask to
   rebase on `upstream/main`, but this checkout had only `origin` configured.
4. Rebase or fast-forward from the configured upstream.
5. Fetch Lean Pool commit
   `c8ddda0a64f21cb019720cdda48c94354d4091e7`.
6. Implement Wave 1 and commit it before beginning the 54,610-line vendor import.

## Exploration provenance

This report was produced from three independent Luna/xhigh audits:

- module dependency closure and source-size analysis;
- chapter-by-chapter OLP coverage and gap analysis;
- licensing, provenance, Git state, version compatibility, and import workflow.

The exploration itself made no source changes and no proof claims beyond those
present in the inspected Lean files. No compatibility build of the copied source
under FormalOLP's current Mathlib pin has yet succeeded, because the source has
not been vendored and the necessary cache was not populated. Compatibility must
therefore be established by Wave 2 rather than assumed.
