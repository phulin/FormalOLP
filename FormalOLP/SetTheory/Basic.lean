import FormalOLP.FirstOrderLogic.SemanticNotions

/-!
# Basic set theory

This module ports the first model-level set-theory chain from Lean Pool's
`FoZfc/Basic.lean` and `FoZfc/Axioms.lean`. The language has no function
symbols and one relation at each arity, with the binary relation interpreted
as membership. The API stops at extensionality, empty-set uniqueness, and
pair uniqueness; it does not assert a full ZF or ZFC model.

The corresponding OLP statements are in
`OpenLogic/content/set-theory/story/extensionality.tex` and the axiom list in
`OpenLogic/content/set-theory/cardinals/milestone.tex`.
-/

namespace FormalOLP.SetTheory

open FirstOrder

universe w

/-- The pure membership language: no functions and one relation at each arity. -/
abbrev Language : FirstOrder.Language :=
  { Functions := fun _ => Empty
    Relations := fun _ => Unit }

/-- The atomic formula expressing membership of the two bound variables. -/
def membershipFormula : FirstOrder.Language.BoundedFormula Language Empty 2 :=
  .rel () ![.var (Sum.inr (0 : Fin 2)), .var (Sum.inr (1 : Fin 2))]

/-- The relation interpreted by a first-order structure as membership. -/
def Mem (S : FirstOrder.Language.Structure Language V) (x y : V) : Prop :=
  (@FirstOrder.Language.Structure.RelMap Language V S 2 ()) ![x, y]

/-- The atomic membership formula has the intended model interpretation. -/
theorem realize_membership (S : FirstOrder.Language.Structure Language V) (a b : V) :
    @FirstOrder.Language.BoundedFormula.Realize Language V S Empty 2
      membershipFormula default ![a, b] ↔ Mem S a b := by
  unfold membershipFormula
  change (@FirstOrder.Language.Relations.boundedFormula Language Empty 2 2 () _).Realize _ _ ↔ _
  rw [FirstOrder.Language.BoundedFormula.realize_rel]
  unfold Mem
  have hv :
      (fun i : Fin 2 =>
        FirstOrder.Language.Term.realize (Sum.elim (default : Empty → V) ![a, b])
          ((![FirstOrder.Language.Term.var (Sum.inr (0 : Fin 2)),
            FirstOrder.Language.Term.var (Sum.inr (1 : Fin 2))] :
              Fin 2 → FirstOrder.Language.Term Language (Empty ⊕ Fin 2)) i)) = ![a, b] := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i
  rw [hv]

/-- Extensionality: sets with the same members are equal. -/
def Extensionality {V : Type w} (mem : V → V → Prop) : Prop :=
  ∀ ⦃a b : V⦄, (∀ z, mem z a ↔ mem z b) → a = b

/-- A model of the membership language satisfying extensionality. -/
structure ModelExtensionality (V : Type w) extends
    FirstOrder.Language.Structure Language V where
  nonempty : Nonempty V
  extensionality : Extensionality (fun x y => Mem toStructure x y)

namespace ModelExtensionality

variable {V : Type w} (M : ModelExtensionality V)

/-- An object with no members. -/
def IsEmptyset (e : V) : Prop := ∀ x, ¬Mem M.toStructure x e

/-- The empty-set axiom as a model-level existence statement. -/
def EmptysetAxiom : Prop := ∃ e : V, IsEmptyset M e

theorem emptyset_unique {e e' : V}
    (he : IsEmptyset M e) (he' : IsEmptyset M e') : e = e' := by
  exact M.extensionality fun z ↦ iff_of_false (he z) (he' z)

theorem emptyset_exists_unique (h : M.EmptysetAxiom) :
    ∃! e : V, IsEmptyset M e := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, he, fun e' he' ↦ (emptyset_unique M (e := e) (e' := e') he he').symm⟩

/-- An object whose members are exactly the two supplied objects. -/
def IsPair (a b p : V) : Prop := ∀ x, Mem M.toStructure x p ↔ x = a ∨ x = b

/-- The pairing axiom as a model-level existence statement. -/
def PairingAxiom : Prop := ∀ a b : V, ∃ p : V, IsPair M a b p

theorem pair_unique {a b p p' : V}
    (hp : IsPair M a b p) (hp' : IsPair M a b p') : p = p' := by
  exact M.extensionality fun z ↦ (hp z).trans (hp' z).symm

theorem pair_exists_unique (h : M.PairingAxiom) (a b : V) :
    ∃! p : V, IsPair M a b p := by
  obtain ⟨p, hp⟩ := h a b
  exact ⟨p, hp, fun p' hp' ↦ (pair_unique M (a := a) (b := b)
    (p := p) (p' := p') hp hp').symm⟩

theorem singleton_unique {a p p' : V}
    (hp : IsPair M a a p) (hp' : IsPair M a a p') : p = p' :=
  pair_unique M hp hp'

theorem singleton_exists_unique (h : M.PairingAxiom) (a : V) :
    ∃! p : V, IsPair M a a p :=
  pair_exists_unique M h a a

end ModelExtensionality

end FormalOLP.SetTheory
