# FormalOLP topic map

FormalOLP follows the subject-level parts in the Open Logic Text and uses
native Lean module names.  The map intentionally has no chapter numbers:
source chapters and sections can change independently of the Lean API.

The current OpenLogic source is the initialized submodule at commit
`1e960beff9ed7835bf3e3f1335e21af3439cd107` from
<https://github.com/OpenLogicProject/OpenLogic>.  The table records the actual
source roots used to derive each aggregator.  A module marked “scaffold” has
scope documentation only; “initial API” identifies the one small theorem
currently proved in Lean.

Each mathematical topic currently has one flat entry module under
`FormalOLP/`.  Future declarations can be organized in a same-name child
directory, such as `FormalOLP/FirstOrderLogic/`, without changing the public
topic entry point.  Editorial source parts that do not define a mathematical
Lean API remain mapped below as documentation-only material.

| Lean module | OpenLogic source path(s) | Current scope |
| --- | --- | --- |
| `FormalOLP.SetsFunctionsRelations` | `OpenLogic/content/sets-functions-relations/sets-functions-relations-complete.tex`; `sets/`; `relations/`; `functions/`; `size-of-sets/`; `arithmetization/`; `infinite/` | Initial API: set absorption; remaining source topics scaffolded |
| `FormalOLP.PropositionalLogic` | `OpenLogic/content/propositional-logic/propositional-logic.tex`; `syntax-and-semantics/` | Scaffold |
| `FormalOLP.FirstOrderLogic` | `OpenLogic/content/first-order-logic/first-order-logic.tex`; `introduction/`; `syntax-and-semantics/`; `models-theories/`; `proof-systems/`; `sequent-calculus/`; `natural-deduction/`; `tableaux/`; `axiomatic-deduction/`; `completeness/`; `beyond/` | Scaffold |
| `FormalOLP.ModelTheory` | `OpenLogic/content/model-theory/model-theory.tex`; `basics/`; `models-of-arithmetic/`; `interpolation/`; `lindstrom/` | Scaffold |
| `FormalOLP.Computability` | `OpenLogic/content/computability/computability.tex`; `recursive-functions/`; `computability-theory/` | Scaffold |
| `FormalOLP.TuringMachines` | `OpenLogic/content/turing-machines/turing-machines.tex`; `machines-computations/`; `undecidability/` | Scaffold |
| `FormalOLP.Incompleteness` | `OpenLogic/content/incompleteness/incompleteness.tex`; `introduction/`; `arithmetization-syntax/`; `representability-in-q/`; `theories-computability/`; `incompleteness-provability/` | Scaffold |
| `FormalOLP.SecondOrderLogic` | `OpenLogic/content/second-order-logic/second-order-logic.tex`; `syntax-and-semantics/`; `metatheory/`; `sol-and-set-theory/` | Scaffold |
| `FormalOLP.LambdaCalculus` | `OpenLogic/content/lambda-calculus/lambda-calculus.tex`; `introduction/`; `syntax/`; `church-rosser/`; `lambda-definability/` | Scaffold |
| `FormalOLP.ManyValuedLogic` | `OpenLogic/content/many-valued-logic/many-valued-logic.tex`; `syntax-and-semantics/`; `three-valued-logics/`; `infinite-valued-logics/`; `sequent-calculus/` | Scaffold |
| `FormalOLP.NormalModalLogic` | `OpenLogic/content/normal-modal-logic/normal-modal-logic.tex`; `syntax-and-semantics/`; `frame-definability/`; `axioms-systems/`; `completeness/`; `filtrations/`; `tableaux/`; `sequent-calculus/` | Scaffold |
| `FormalOLP.AppliedModalLogic` | `OpenLogic/content/applied-modal-logic/applied-modal-logic.tex`; `epistemic-logic/`; `temporal-logic/` | Scaffold |
| `FormalOLP.IntuitionisticLogic` | `OpenLogic/content/intuitionistic-logic/intuitionistic-logic.tex`; `introduction/`; `semantics/`; `soundness-completeness/`; `tableaux/` | Scaffold |
| `FormalOLP.Counterfactuals` | `OpenLogic/content/counterfactuals/counterfactuals.tex`; `introduction/`; `minimal-change-semantics/` | Scaffold |
| `FormalOLP.SetTheory` | `OpenLogic/content/set-theory/set-theory.tex`; `story/`; `z/`; `ordinals/`; `spine/`; `replacement/`; `ord-arithmetic/`; `cardinals/`; `card-arithmetic/`; `choice/` | Scaffold |
| `FormalOLP.Methods` | `OpenLogic/content/methods/methods.tex`; `proofs/`; `induction/` | Scaffold |
| `FormalOLP.ProofTheory` | `OpenLogic/content/proof-theory/proof-theory.tex`; `sequent-calculus/`; `cut-elimination/`; `natural-deduction/`; `normalization/`; `propositions-as-types/`; `proof-search/` | Scaffold |
| documentation only (no Lean module) | `OpenLogic/content/history/history.tex`; `biographies/`; `set-theory/` | Editorial and historical context; retained for source mapping |
| documentation only (no Lean module) | `OpenLogic/content/reference/reference.tex`; `greek-alphabet/`; `fraktur-alphabet/` | Reference and notation material; retained for source mapping |

## Status and dependency boundary

The root `FormalOLP.lean` imports the mathematical topic aggregators so the
module tree is visible to the build.  History and Reference remain mapped as
documentation-only source parts and have no empty Lean modules.  The scaffold
does not import Lean Pool.  Lean Pool
will be added only when a specific formalization needs it, with its own
provenance record.  The initial set result uses Mathlib's `Set` lattice and
does not assert that any textbook syntax, valuation, proof calculus, or model
is definitionally the same as a future imported development.

The current initial API is the absorption proposition from
`OpenLogic/content/sets-functions-relations/sets/proofs-about-sets.tex`:

```lean
FormalOLP.SetsFunctionsRelations.intersection_union_absorption
```

The source text is not copied into Lean files.  This map is source attribution
and planning metadata only.

## Open Logic Project attribution

The Open Logic Text source is copyright the Open Logic Project and is licensed
under the [Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/).
The repository's source and license are at
[`OpenLogic/README.md`](../OpenLogic/README.md) and
[`OpenLogic/LICENSE.md`](../OpenLogic/LICENSE.md).  When FormalOLP distributes
adapted textbook material, it must preserve that attribution, identify changes,
and link to the license.  This CC BY 4.0 attribution is intentionally separate
from the licenses and provenance records for any future Lean or Lean Pool code;
the scaffold currently vendors no Lean Pool source.
