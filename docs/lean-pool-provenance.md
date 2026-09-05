# FormalOLP provenance and licensing ledger

Status: policy and discovery ledger; no Lean Pool source is copied yet.

Date of this audit: 2026-09-05

This document records where source comes from, which exact revisions were
inspected, and what remains to be verified before source is copied into
FormalOLP. FormalOLP has no Lean Pool package dependency: selected source
files will be copied into the repository only when an OLP declaration needs
them. It is deliberately more conservative than a license summary: a
license named by Lean Pool is recorded as a Lean Pool claim, and a license
observed in an upstream file is recorded with the exact upstream revision. An
upstream revision observed today is not silently treated as the revision from
which source revisions Lean Pool recorded for its files.

## Current state

The repository currently contains no <code>LeanPool/</code> directory and no copied Lean
Pool files. The vendored-source inventory is therefore empty:

| Local inventory | State at this audit |
| --- | --- |
| <code>LeanPool/</code> source files | none |
| Lean Pool project entries | none |
| copied third-party license files | none |
| local modifications to third-party Lean source | none |
| provenance rows requiring a file manifest | none |

The working tree does contain the initial OLP topic scaffold under
<code>FormalOLP/</code>. Its module names and source mapping are recorded in
[<code>topic-map.md</code>](topic-map.md). The scaffold uses Mathlib where it has an
initial set API and contains no copied Lean Pool source. This is an intentional boundary:
the topic API is established from the Open Logic source before reuse choices
are made.

## Provenance policy

FormalOLP follows this order for a future Lean Pool reuse:

1. Define or extend the relevant native OLP topic module in <code>FormalOLP/</code>, with
   its source path in <code>docs/topic-map.md</code>.
2. State the concrete missing declaration or bridge that motivates reuse. A
   project is not copied merely because it is related to a topic.
3. Select the smallest complete Lean Pool source closure that supplies that
   declaration. If a closure is too coarse, record why its extra modules are
   unavoidable.
4. Resolve the exact Lean Pool commit, inspect its <code>projects.yml</code>, <code>NOTICE</code>,
   per-file headers, and source manifest, and record the selected project's
   upstream source revision if Lean Pool records one.
5. If the Lean Pool metadata does not record the upstream source revision, do
   not infer it from dates, branch names, or a current upstream checkout. Mark
   it unresolved and resolve it by comparing the files or by obtaining the
   source record before copying.
6. Copy the complete selected closure into preserved <code>LeanPool/...</code> module
   paths in a dedicated vendor commit. Preserve headers, namespaces, and
   project-specific adaptations where practical. Copied files may retain
   ordinary Lean imports within that closure; this does not create a Lean Pool
   package dependency. Copy the applicable license and attribution notices
   with the source.
7. Record every local modification in a follow-up compatibility row, then
   build the copied entry module and required closure against the FormalOLP
   dependency graph.
8. Add the OLP bridge only after the copied source and its provenance row are
   reviewable. The bridge must state the OLP theorem and prove any hypothesis
   translation explicitly.

Every copied project row must have these fields:

| Field | Required content |
| --- | --- |
| <code>project</code> | Lean Pool project slug and entry module |
| <code>local_paths</code> | Exact copied paths or a committed generated manifest of paths |
| <code>pool_source</code> | Immutable Lean Pool URL and full commit SHA |
| <code>upstream_source</code> | Repository URL and full source SHA; <code>unresolved</code> is allowed only while the row is pending |
| <code>environment</code> | Lean toolchain, Mathlib revision, and any additional package revisions used to verify it |
| <code>license</code> | License applying to the copied source, plus the evidence URL/path |
| <code>attribution</code> | Copyright holders, authors, and required notices |
| <code>modifications</code> | <code>none</code> for byte-identical vendor commit, otherwise each changed path and reason |
| <code>verification</code> | Closure/build checks and date; do not call an unbuilt copy verified |
| <code>status</code> | <code>candidate</code>, <code>pending-source-ref</code>, <code>copied</code>, <code>ported</code>, or <code>rejected</code> |

The path manifest should contain one row per copied file with its Lean Pool
blob SHA and local blob SHA. A future provenance check should fail when a file
under <code>LeanPool/</code> is absent from that manifest, when a manifest row lacks a
license and source SHA, or when a modified file has no modification record.
There is no verification script yet because there is no vendored inventory for
it to check; adding a script becomes useful with the first source copy.

## Reproducible dependency environment

The current build scaffold records the exact direct pins in
[<code>lakefile.toml</code>](../lakefile.toml) and [<code>lean-toolchain</code>](../lean-toolchain):

| Dependency | Immutable revision | Evidence and license status |
| --- | --- | --- |
| Lean | <code>leanprover/lean4:v4.34.0-rc2</code> | Directly recorded in <code>lean-toolchain</code>; the compiler's own license is not a vendored FormalOLP source license. |
| Mathlib | <code>5fcc6656691ed31965746c369f41fa75e567ac9d</code> | Directly pinned in <code>lakefile.toml</code>; local <code>.lake/packages/mathlib/LICENSE</code> is Apache-2.0. [Immutable revision](https://github.com/leanprover-community/mathlib4/tree/5fcc6656691ed31965746c369f41fa75e567ac9d), [license at that commit](https://github.com/leanprover-community/mathlib4/blob/5fcc6656691ed31965746c369f41fa75e567ac9d/LICENSE). |
| Tau Ceti | <code>8525a756ec80a2338bf75a42ca80f19c47ead468</code> | Directly pinned in <code>lakefile.toml</code>; local <code>.lake/packages/TauCeti/LICENSE</code> is Apache-2.0. [Immutable revision](https://github.com/TauCetiProject/TauCeti/tree/8525a756ec80a2338bf75a42ca80f19c47ead468), [license at that commit](https://github.com/TauCetiProject/TauCeti/blob/8525a756ec80a2338bf75a42ca80f19c47ead468/LICENSE). |

The root <code>lake-manifest.json</code> is now present in the shared working tree and
records the Tau Ceti and Mathlib revisions above, but it remains an uncommitted
change at this audit. The resolved Tau Ceti checkout also contains a manifest
with the same direct Mathlib revision. The exact pins above are the facts
currently verified from the scaffold, not an assertion that every future
package remains at those revisions.

The resolved transitive package licenses were also checked from the local
detached checkouts under <code>.lake/packages/</code>. The exact revision for every
package is in the root <code>lake-manifest.json</code>; the license grouping below
records the license file found at that resolved checkout:

| License observed locally | Resolved packages | Evidence |
| --- | --- | --- |
| Apache-2.0 | <code>TauCeti</code>, <code>mathlib</code>, <code>plausible</code>, <code>LeanSearchClient</code>, <code>importGraph</code>, <code>proofwidgets</code>, <code>aesop</code>, <code>Qq</code>, and <code>batteries</code> | Each checkout has an Apache-2.0 <code>LICENSE</code>; Mathlib is <code>5fcc6656691ed31965746c369f41fa75e567ac9d</code> and Tau Ceti is <code>8525a756ec80a2338bf75a42ca80f19c47ead468</code>. |
| MIT | <code>Cli</code> | <code>.lake/packages/Cli/LICENSE</code> is the MIT License and carries Copyright (c) 2021 mhuisi; the resolved revision is <code>ab3a82db9fea14cf0fd7f5a2de650f4b534640af</code> ([license at that commit](https://github.com/leanprover/lean4-cli/blob/ab3a82db9fea14cf0fd7f5a2de650f4b534640af/LICENSE)). |

These are licenses of external dependency sources. They do not select or
imply a license for new FormalOLP code.

Lean Pool's inspected snapshot uses a different environment and must not be
treated as the FormalOLP dependency graph:

| Item | Lean Pool snapshot value |
| --- | --- |
| Pool commit | [<code>c8ddda0a64f21cb019720cdda48c94354d4091e7</code>](https://github.com/Vilin97/lean-pool/tree/c8ddda0a64f21cb019720cdda48c94354d4091e7) |
| Lean toolchain | <code>leanprover/lean4:v4.34.0-rc1</code> |
| Mathlib | <code>de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11</code> |
| Pool metadata | [<code>lakefile.toml</code>](https://github.com/Vilin97/lean-pool/blob/c8ddda0a64f21cb019720cdda48c94354d4091e7/lakefile.toml), [<code>lake-manifest.json</code>](https://github.com/Vilin97/lean-pool/blob/c8ddda0a64f21cb019720cdda48c94354d4091e7/lake-manifest.json), [<code>NOTICE</code>](https://github.com/Vilin97/lean-pool/blob/c8ddda0a64f21cb019720cdda48c94354d4091e7/NOTICE), and [<code>projects.yml</code>](https://github.com/Vilin97/lean-pool/blob/c8ddda0a64f21cb019720cdda48c94354d4091e7/LeanPool/projects.yml) |

## Lean Pool candidate ledger

These are candidates identified in the inspected Pool metadata. They are not
copied entries. The Pool <code>projects.yml</code> at this snapshot gives the project
license and repository, but does not give an upstream commit for these six
projects. The “observed upstream head” values below are immutable refs checked
on 2026-09-05 for license inspection and discovery only; they are not claimed
to be the source revision recorded for Lean Pool's copy.

| Candidate | OLP use trigger | Pool license record | Upstream URL | Observed upstream head and license evidence | Source revision used by Pool | Status |
| --- | --- | --- | --- | --- | --- | --- |
| <code>incompleteness</code> / <code>LeanPool.Incompleteness</code> | A bridge needs its arithmetization or provability APIs after the OLP incompleteness module states the textbook theorem | Apache-2.0 (<code>projects.yml</code>, <code>NOTICE</code>) | [FormalizedFormalLogic/Incompleteness](https://github.com/FormalizedFormalLogic/Incompleteness) | [<code>52232b787a6e3a048ccb447383a842a84b711bb8</code>](https://github.com/FormalizedFormalLogic/Incompleteness/tree/52232b787a6e3a048ccb447383a842a84b711bb8); <code>LICENSE</code> begins Apache-2.0 | Not recorded in Pool metadata; resolve before copying | <code>candidate</code> |
| <code>fo-zfc</code> / <code>LeanPool.FoZfc</code> | An OLP first-order set-theory or model-theory declaration needs this <code>FirstOrder.Language</code> development | Apache-2.0 (<code>projects.yml</code>, <code>NOTICE</code>) | [ishiut/fo_zfc](https://github.com/ishiut/fo_zfc) | [<code>bc2453ee286e4375827b17cfc0e4a0187ee0e09e</code>](https://github.com/ishiut/fo_zfc/tree/bc2453ee286e4375827b17cfc0e4a0187ee0e09e); <code>LICENSE</code> begins Apache-2.0 | Not recorded in Pool metadata; resolve before copying | <code>candidate</code> |
| <code>zflean</code> / <code>LeanPool.ZFLean</code> | An OLP set-theory declaration needs the concrete <code>ZFSet</code> development | Apache-2.0 (<code>projects.yml</code>, <code>NOTICE</code>) | [VTrelat/ZFLean](https://github.com/VTrelat/ZFLean) | [<code>ae928234e7ed6b26241344ef4ba6d7cf98c0ed91</code>](https://github.com/VTrelat/ZFLean/tree/ae928234e7ed6b26241344ef4ba6d7cf98c0ed91); <code>LICENSE</code> begins Apache-2.0 | Not recorded in Pool metadata; resolve before copying | <code>candidate</code> |
| <code>computability</code> / <code>LeanPool.Computability</code> | An OLP computability declaration specifically needs oracle computation, Turing degrees, or jumps | Apache-2.0 (<code>projects.yml</code>, <code>NOTICE</code>) | [tannerduve/computability](https://github.com/tannerduve/computability) | [<code>e07f3a17c5285e777af6b5b08fb4059fdfb28379</code>](https://github.com/tannerduve/computability/tree/e07f3a17c5285e777af6b5b08fb4059fdfb28379); <code>LICENSE</code> begins Apache-2.0 | Not recorded in Pool metadata; resolve before copying | <code>candidate</code> |
| <code>formalization-of-bounded-arithmetic</code> / <code>LeanPool.FormalizationOfBoundedArithmetic</code> | An OLP arithmetic bridge requires its bounded-arithmetic model interfaces | MIT (<code>projects.yml</code>, <code>NOTICE.extra.yml</code>) | [ruplet/formalization-of-bounded-arithmetic](https://github.com/ruplet/formalization-of-bounded-arithmetic) | [<code>0477b134d8756fcf312c3b88c1f449e8eec2fea1</code>](https://github.com/ruplet/formalization-of-bounded-arithmetic/tree/0477b134d8756fcf312c3b88c1f449e8eec2fea1); [<code>LICENSE.txt</code>](https://github.com/ruplet/formalization-of-bounded-arithmetic/blob/0477b134d8756fcf312c3b88c1f449e8eec2fea1/LICENSE.txt) is MIT with the literal template copyright line | Not recorded in Pool metadata; resolve before copying | <code>candidate</code> |
| <code>partial-combinatory-algebras</code> / <code>LeanPool.PartialCombinatoryAlgebras</code> | An OLP lambda-calculus or realizability bridge specifically needs PCA infrastructure | MIT (<code>projects.yml</code>, <code>NOTICE.extra.yml</code>) | [andrejbauer/partial-combinatory-algebras](https://github.com/andrejbauer/partial-combinatory-algebras) | [<code>8a97af138268bfe1a3bd0e2e21333bd70d14c4ee</code>](https://github.com/andrejbauer/partial-combinatory-algebras/tree/8a97af138268bfe1a3bd0e2e21333bd70d14c4ee); [<code>LICENSE</code>](https://github.com/andrejbauer/partial-combinatory-algebras/blob/8a97af138268bfe1a3bd0e2e21333bd70d14c4ee/LICENSE) is MIT and names Andrej Bauer | Not recorded in Pool metadata; resolve before copying | <code>candidate</code> |

The candidate list does not authorize copying all six projects. In
particular, the earlier proposal to copy the full 183-module
<code>LeanPool.Incompleteness</code> closure followed by five adjacent projects is
superseded. A future row must identify the OLP declaration that requires the
closure and report the actual selected module count and file hashes.

## First-order semantics reuse audit

The first concrete OLP target reviewed against the pinned source is the
generic semantics sequence in the textbook's first-order chapter:
<code>syntax-and-semantics/first-order-languages.tex</code>,
<code>terms-formulas.tex</code>, <code>structures.tex</code>,
<code>assignments.tex</code>, <code>satisfaction.tex</code>, and
<code>semantic-notions.tex</code>. These sections define terms, formulas,
structures, variable assignments, term evaluation, satisfaction, validity,
entailment, satisfiability, and theory models. The current
<code>FormalOLP.FirstOrderLogic</code> and <code>FormalOLP.ModelTheory</code>
modules have no declarations that require a third-party source closure yet.

The pinned Mathlib revision already supplies the generic API needed for this
target. <code>Mathlib.ModelTheory.Basic</code> defines
<code>FirstOrder.Language</code> and <code>Language.Structure</code>;
<code>Mathlib.ModelTheory.Syntax</code> defines <code>Term</code>, locally
nameless <code>BoundedFormula</code>, <code>Formula</code>,
<code>Sentence</code>, and <code>Theory</code>, together with substitution and
relabelling; and <code>Mathlib.ModelTheory.Semantics</code> defines
<code>Term.realize</code>, <code>BoundedFormula.Realize</code>, sentence
realization, and theory models. This API matches the mathematical target
while making the textbook's variable-assignment and satisfaction lemmas
explicit in a small FormalOLP adapter. Tau Ceti contributes no dedicated
first-order syntax or semantics module in the resolved checkout. Therefore
the initial semantics target should use Mathlib directly; copying Lean Pool
at this stage would add a translation burden without supplying a missing
generic result.

The relevant Lean Pool candidate, <code>fo-zfc</code>, is a later set-theory
dependency, not a generic first-order semantics library. At [Pool commit
<code>c8ddda0a64f21cb019720cdda48c94354d4091e7</code>](https://github.com/Vilin97/lean-pool/tree/c8ddda0a64f21cb019720cdda48c94354d4091e7),
its entry module is <code>LeanPool.FoZfc</code>; the source was introduced by
[Pool vendor commit
<code>b161489d3ebf967f8e933aa626bbdf030b335481</code>](https://github.com/Vilin97/lean-pool/commit/b161489d3ebf967f8e933aa626bbdf030b335481)
and consists of this complete seven-file closure:

| Pool path | Role |
| --- | --- |
| <code>LeanPool/FoZfc.lean</code> | entry module importing the closure |
| <code>LeanPool/FoZfc/Basic.lean</code> | <code>LZFC</code>, set-membership syntax, and model base |
| <code>LeanPool/FoZfc/FixedSnoc.lean</code> | finite tuple and <code>Fin.snoc</code> lemmas |
| <code>LeanPool/FoZfc/BoundedFormulaOps.lean</code> | bounded-formula operations and realization lemmas |
| <code>LeanPool/FoZfc/Tostring.lean</code> | display functions for the ZFC syntax |
| <code>LeanPool/FoZfc/Axioms.lean</code> | internal and external ZF axiom classes |
| <code>LeanPool/FoZfc/Replacement.lean</code> | replacement and <code>ModelZF</code> development |

The Pool import commit states that this closure was ported from Lean
<code>v4.22.0-rc3</code> to Pool's <code>v4.30.0-rc2</code>; the inspected Pool
snapshot itself uses <code>v4.34.0-rc1</code> and Mathlib revision
<code>de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11</code>. The closure imports
Mathlib's <code>ModelTheory.Basic</code>, <code>Syntax</code>, and
<code>Semantics</code>, but specializes them to
<code>FirstOrder.Language.LZFC</code> and ZF model classes. It is therefore
unsuitable as the first generic semantics source. If a later OLP declaration
specifically formalizes the textbook's set-theory chapter and needs
<code>ModelZF</code> or <code>ext_induction</code>, this seven-file closure is
the smallest complete Pool closure identified so far; it should be copied
only after an OLP theorem trigger and a build against FormalOLP's different
pinned Mathlib revision.

Pool's <code>projects.yml</code> records <code>fo-zfc</code> as Apache-2.0,
names Tetsuya Ishiu as author, and gives the upstream repository
<code>https://github.com/ishiut/fo_zfc</code>; Pool's <code>NOTICE</code> lists
the same project in the Apache-2.0 section. The upstream repository's
observed commit
<code>bc2453ee286e4375827b17cfc0e4a0187ee0e09e</code> contains an Apache-2.0
<code>LICENSE</code> and the same author attribution. Pool metadata does not
record the upstream source commit used by the vendor import, so
<code>bc2453...</code> remains discovery and license evidence only, not a
source-revision claim. A future vendor row must resolve that source SHA,
preserve the per-file Ishiu headers and Apache notice, and record the Pool
port as a modification before copying.

Decision: do not copy <code>fo-zfc</code> for the initial first-order
semantics target. Keep it as a <code>candidate</code> for a named OLP
set-theory/model-theory declaration; promote its status to
<code>pending-source-ref</code> only once that declaration is selected and the
Pool port's upstream source SHA must be resolved.

The Pool snapshot's own <code>NOTICE</code> says that its root aggregation is Apache-2.0
while original authors retain copyright and the MIT projects retain their
original notices. FormalOLP should preserve that distinction. A Pool-level
Apache label does not erase a project's original MIT notice, author attribution,
or file headers.

## Open Logic source attribution

The Open Logic source is a separate Git submodule at commit
<code>1e960beff9ed7835bf3e3f1335e21af3439cd107</code>, from
<https://github.com/OpenLogicProject/OpenLogic>. Its
[<code>README.md</code>](../OpenLogic/README.md) and
[<code>LICENSE.md</code>](../OpenLogic/LICENSE.md) state that the Open Logic Text is
licensed under the [Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/).

The CC BY 4.0 attribution applies to adapted Open Logic Text material and is
kept separate from Lean dependency and Lean Pool notices. The FormalOLP
scaffold records source paths and topic mappings but does not copy textbook
prose. Any future adapted textbook material must identify the source, describe
changes, retain attribution, and link the license.

The license for new FormalOLP Lean code is intentionally undecided here. This
ledger does not select a license for the user, and no dependency license should
be presented as the license of new FormalOLP code.

## Wave record

The first three waves are now defined by the revised order of work:

| Wave | Scope | Current progress | Exit evidence |
| --- | --- | --- | --- |
| 1. OLP topic scaffold | Create native module names and source mappings from OLP topics before reuse decisions | Working-tree scaffold present: <code>FormalOLP.lean</code>, the topic modules listed in [<code>topic-map.md</code>](topic-map.md), and one small set API. The files are not committed at this audit. | All topic aggregators build, each maps to real OLP paths, and no copied Lean Pool source is referenced. |
| 2. Build environment | Pin Lean, Mathlib, and Tau Ceti and build the scaffold | Working-tree pins and the generated root <code>lake-manifest.json</code> are verified. <code>lake build</code> passes for 451 jobs, and <code>lake env lean -E warning test/Compatibility.lean</code> passes while importing Tau Ceti and FormalOLP together. These files remain uncommitted at this audit. | Commit <code>lakefile.toml</code>, <code>lean-toolchain</code>, the resolved root manifest, and the compatibility smoke test; rerun the clean build. |
| 3. Need-driven Lean Pool source copying | Copy only the smallest complete Pool closure needed by a named OLP declaration | Not started. <code>LeanPool/</code> is absent and the candidate rows above remain uncopied. | A candidate has an OLP trigger, immutable Pool SHA, resolved upstream source SHA, license evidence, path manifest, and a passing isolated build. |

This status intentionally distinguishes “present in the shared working tree”
from “committed” and “verified as vendored.” It should be updated when the
build agent commits the environment and when the first Lean Pool project is
actually selected.

## Required notice for the first vendor commit

The first vendor commit should include a <code>LeanPool/NOTICE</code> or equivalent
ledger reference that names:

- the exact Lean Pool commit and immutable URL;
- each copied project and its original upstream URL and source SHA;
- the applicable Apache-2.0 or MIT license evidence;
- original author/copyright notices and any Pool <code>NOTICE</code> text;
- the exact copied paths and whether they are byte-identical;
- the FormalOLP compatibility changes made later; and
- the OLP source attribution separately when a bridge adapts textbook material.

Until that commit exists, no README, build file, or theorem should describe
Lean Pool as vendored or claim that a Lean Pool license has been applied to
FormalOLP code.
