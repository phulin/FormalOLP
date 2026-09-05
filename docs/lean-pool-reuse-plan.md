# Lean Pool reuse plan for FormalOLP

Status: revised implementation plan

Date: 2026-09-05

This plan follows the current repository order: establish an Open Logic
Project (OLP) topic scaffold with native FormalOLP module names, pin and build
the Tau Ceti and Mathlib environment, then copy every complete Lean Pool
closure that directly matches a named OLP topic. The copied files may retain
their internal Lean imports, but FormalOLP will not depend on a Lean Pool
package. The provenance and
licensing rules for that process live in
[lean-pool-provenance.md](lean-pool-provenance.md).

## Decision

FormalOLP starts with its own topic boundaries. The current mathematical
aggregators are:

- FormalOLP.SetsFunctionsRelations
- FormalOLP.PropositionalLogic
- FormalOLP.FirstOrderLogic
- FormalOLP.ModelTheory
- FormalOLP.Computability
- FormalOLP.TuringMachines
- FormalOLP.Incompleteness
- FormalOLP.SecondOrderLogic
- FormalOLP.LambdaCalculus
- FormalOLP.ManyValuedLogic
- FormalOLP.NormalModalLogic
- FormalOLP.AppliedModalLogic
- FormalOLP.IntuitionisticLogic
- FormalOLP.Counterfactuals
- FormalOLP.SetTheory
- FormalOLP.Methods
- FormalOLP.ProofTheory

The exact source paths and current scope for these modules are maintained in
[topic-map.md](topic-map.md). History and Reference are source-mapped
documentation parts without empty Lean modules. This gives the project a
stable native API surface while leaving room for each topic to choose the
representation that matches the textbook.

The scaffold has one small set API using Mathlib's Set lattice and now carries
nine complete topic-matched Pool closures. The copied corpus is reusable source
coverage; it is not evidence that a textbook syntax, valuation, proof calculus,
or model has already been formalized in FormalOLP.

The earlier one-theorem gate is superseded by the user's broad request for
topic-matched source. The copied set is still bounded by the seventeen OLP
entries: project-specific namespaces, adaptations, and licenses remain distinct
from new FormalOLP code, and every OLP bridge must be proved explicitly.

## Goals and boundaries

The goal is textbook-faithful formalization with reusable interfaces. Each OLP
topic should first state the definitions and theorem shapes that the source
requires. Existing developments can then discharge a precisely identified
piece of that interface.

A related Lean Pool project is selected when all of the following hold:

1. The project directly matches one or more named OLP topics in
   <code>docs/topic-map.md</code>.
2. The proposed project supplies an API that can be adapted without silently
   changing a future OLP statement.
3. The selected source closure is complete and builds as a local source tree.
4. Its immutable Pool revision, upstream source revision, license evidence,
   copied paths, and modifications can be recorded.
5. The copied entry and required closure build against FormalOLP's pinned
   Mathlib and Tau Ceti dependency graph.

A Lean Pool theorem is not automatically an OLP theorem. For example, an
incompleteness result with hypotheses involving R₀, IΣ₁, Sigma1Sound, or
Delta1Definable needs explicit bridges before it can support an OLP statement
about Q, computable axiomatizability, consistency, or representability.
Likewise, FoZfc's Mathlib FirstOrder.Language and Lean Pool's LO.FirstOrder
syntax are different interfaces until a translation is proved.

The license of new FormalOLP code remains undecided. The Open Logic Text's CC
BY 4.0 attribution, Tau Ceti and Mathlib's Apache-2.0 notices, and each future
Lean Pool project's original notices are separate records. This plan does not
choose a license for the user.

## Wave 1: OLP topic scaffold

Wave 1 creates the module tree from the OLP source. It is complete when the
aggregators build and every mapping points to actual source paths, even where a
topic has no declarations yet.

The shared working tree already contains:

- the 17 mathematical topic aggregators listed above;
- the public FormalOLP root module;
- docs/topic-map.md with the source-to-module table;
- the initial set absorption API in FormalOLP.SetsFunctionsRelations; and
- the copied topic-matched Lean Pool closures under LeanPool/.

The files are currently working-tree changes and have not been committed at
the time of this report. The scaffold's source attribution points to the
OpenLogic submodule at commit
1e960beff9ed7835bf3e3f1335e21af3439cd107. The Open Logic repository README
and LICENSE identify the text as CC BY 4.0. FormalOLP copies no textbook
prose in this wave.

The root module imports the mathematical topic aggregators so the module tree
is visible to Lake. It does not import documentation-only History or Reference
modules. The separate LeanPool library target exposes the copied closures
without making them part of the FormalOLP root API.

The first substantive FOL API is now present in
`FormalOLP.FirstOrderLogic.SemanticNotions`. It follows the textbook's
`syntax-and-semantics/semantic-notions.tex` target and uses Mathlib's existing
`FirstOrder.Language` syntax and semantics directly. The API defines semantic
consequence and satisfiability for theories of `L.Sentence`, then proves
membership, monotonicity, equivalence with unsatisfiability after adjoining a
negation, and the semantic deduction theorem. Mathlib's bundled
`Theory.ModelType` carries `Nonempty`, matching the textbook's explicit
non-empty-domain convention. The current declarations intentionally quantify
only over sentences; no theorem silently treats an open `L.Formula α` as a
sentence, and future open-formula work must use Mathlib's assignment-aware
`T ⊨ᵇ φ` interface or an explicit constants translation.

The FormalOLP-only module and aggregate pass `lake env lean -E warning
FormalOLP/FirstOrderLogic/SemanticNotions.lean` and `lake build FormalOLP` on
the pinned FormalOLP environment. This result does not include the pending
Lean Pool aggregate, and this API does not require Lean Pool source.

## Wave 2: reproducible build environment

Wave 2 makes the scaffold build on one dependency graph:

| Item | Pin in the current scaffold |
| --- | --- |
| Lean | leanprover/lean4:v4.34.0-rc2 |
| Mathlib | 5fcc6656691ed31965746c369f41fa75e567ac9d |
| Tau Ceti | 8525a756ec80a2338bf75a42ca80f19c47ead468 |

These pins are present in lakefile.toml and lean-toolchain. The Tau Ceti
checkout and Mathlib checkout are available under .lake/packages, and their
license files identify Apache-2.0. `lake build FormalOLP` passes for the
current scaffold; the default aggregate also includes the vendored Lean Pool
target and remains pending while its Incompleteness entry is investigated.

At this report's inspection, the root lake-manifest.json is present in the
shared working tree and records the direct pins, but it is still uncommitted.
The build agent should commit it and rerun a clean build from the resolved
manifest. The direct pins and root transitive lock are therefore verified in
the working tree, but are not yet committed artifacts.

Lean Pool's inspected snapshot is a separate environment:

- Pool commit c8ddda0a64f21cb019720cdda48c94354d4091e7;
- Lean leanprover/lean4:v4.34.0-rc1; and
- Mathlib de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11.

Those values come from the Pool lakefile and manifest. They are evidence about
the source snapshot, not pins for FormalOLP. The immutable Pool metadata and
license links are listed in the provenance ledger.

## Wave 3: scaffold-matched Lean Pool reuse

The broad request selected nine complete closures whose tags and declarations
directly match the seventeen OLP topic entries. They are copied under
<code>LeanPool/</code> at Pool commit
<code>c8ddda0a64f21cb019720cdda48c94354d4091e7</code>:

| Entry | OLP topic coverage | Closure |
| --- | --- | ---: |
| <code>LeanPool.Incompleteness</code> | FirstOrderLogic, ModelTheory, Incompleteness, NormalModalLogic, IntuitionisticLogic, ProofTheory | 183 files / 54,610 lines |
| <code>LeanPool.FoZfc</code> | FirstOrderLogic, ModelTheory, SetTheory | 7 / 2,221 |
| <code>LeanPool.ZFLean</code> | SetTheory, SetsFunctionsRelations | 13 / 8,637 |
| <code>LeanPool.FormalizationOfBoundedArithmetic</code> | Incompleteness, ModelTheory | 21 / 5,973 |
| <code>LeanPool.PartialCombinatoryAlgebras</code> | LambdaCalculus, Computability | 7 / 1,293 |
| <code>LeanPool.Computability</code> | Computability, TuringMachines, Incompleteness | 7 / 1,554 |
| <code>LeanPool.Lean4GlCoalgebras</code> | NormalModalLogic, ModelTheory, ProofTheory, Incompleteness | 18 / 12,510 |
| <code>LeanPool.LeanModelChecking</code> | AppliedModalLogic | 8 / 2,508 |
| <code>LeanPool.Lentil</code> | AppliedModalLogic | 44 / 5,560 |

Current vendor verification is partial: eight entry builds pass
(Computability, FoZfc, FormalizationOfBoundedArithmetic,
PartialCombinatoryAlgebras, ZFLean, Lean4GlCoalgebras, LeanModelChecking,
and Lentil).  The Incompleteness entry remains blocked while the inherited
<code>Formula</code>/<code>Functions</code> performance issue is investigated,
and the aggregate compatibility build has not passed.  The closure counts in
the table are the pinned Pool snapshot counts; compatibility edits and their
current hashes are tracked separately in the manifest.

This copy provides reusable source coverage. It does not formalize the OLP
definitions or theorem statements by itself. The nine entry modules use
project-specific syntax and namespaces; any OLP bridge must state the
translation and its hypotheses explicitly. The pinned Pool metadata omits the
upstream source commit for these nine projects, so each manifest row records
<code>upstream_sha=unresolved</code> until that source relation is established.
The Pool <code>LICENSE</code>, generated <code>NOTICE</code>, and source
<code>NOTICE.extra.yml</code> are preserved under <code>third_party/lean-pool/</code>;
five Mathlib compatibility edits are recorded
with original and current hashes in [<code>docs/lean-pool-manifest.tsv</code>](lean-pool-manifest.tsv).

The audit also reviewed the ten optional projects from the earlier plan.
MatchingLogic, PumpingCfg, SetTheory, and PCFTheory remain gated because they
do not yet match a named textbook calculus or declaration; Borel determinacy,
DomainTheory, and MRiscX are outside the current OLP subject map. Their exact
closure counts and reasons are recorded in the provenance ledger. Copying them
requires a future topic addition and a new complete-closure ledger row.

## Reuse and bridge design

Preserve upstream namespaces and expose OLP-facing interfaces in small
FormalOLP modules. Use explicit adapter lemmas for:

- Mathlib FirstOrder.Language and LO.FirstOrder syntax;
- textbook Q and any imported arithmetic theory;
- computably axiomatized theories and Delta1Definable theories;
- textbook consistency, completeness, and representability terminology;
- concrete Turing machines and oracle or partial computation; and
- ordinary lambda calculus and combinatory algebras.

Each adapter should make changed hypotheses visible. Build a chain of small
named lemmas, then state the OLP theorem at the end of the chain. Avoid a
wrapper that merely renames an imported theorem.

## Verification gates

A scaffold wave must pass:

1. A clean Lake build of the root and all topic aggregators.
2. A check that the root imports the intended mathematical modules and no
   Lean Pool source.
3. A source-map review against the pinned OpenLogic submodule.
4. Axiom and warning checks appropriate to the current project policy.

A Lean Pool vendor wave must additionally pass:

1. A build of the selected entry module and complete selected closure.
2. An aggregate build with FormalOLP, Tau Ceti, Mathlib, and the vendor.
3. Closure and external-import checks, with the copied closure's internal Lean
   imports resolved locally and no Lean Pool package dependency.
4. A path-manifest check covering every copied source file.
5. License, header, attribution, and modification checks.
6. The repository's axiom, warning, and forbidden-source checks.
7. Namespace and notation collision checks.
8. A test that the OLP-facing theorem statement is the textbook claim with
   explicit hypotheses.

Do not add a broad whole-Pool target. Do not solve slow proofs by increasing
maxHeartbeats; split or adapt declarations according to AGENTS.md.

## Later waves

Wave 4 develops textbook-fidelity bridges and the first substantive OLP
theorems after a Wave 3 source copy has a concrete use. Candidate bridge areas are
the Q/R₀ and computability hypotheses, syntax-framework translations, and the
distinction between textbook computation and imported oracle or PCA models.

Wave 5 considers additional Pool projects only when a named OLP theorem needs
them. Optional modal, temporal, language, or set-theory projects remain gated
by actual declarations. No project is copied solely to increase the amount
of copied mathematics.

## Commit sequence

Use the repository's Conventional Commits-ish convention:

1. Commit the topic scaffold and source map.
2. Commit the pinned build environment and resolved root manifest.
3. Commit provenance verification support when the first vendor inventory
   exists.
4. Commit one byte-identical vendor snapshot per selected Lean Pool closure.
5. Commit compatibility ports separately, with changed paths recorded.
6. Commit FormalOLP bridges and OLP-facing theorem statements separately.

Each vendor commit body should name the immutable Pool SHA, upstream repository
and source SHA, license evidence, copied closure, and byte-identity status.
