import FormalOLP.FirstOrderLogic

/-!
# Incompleteness

This module starts the arithmetic side of the OLP incompleteness chapter with
an explicit first-order presentation of Robinson arithmetic.  The language,
the seven usual axioms of `Q`, and its standard natural-number structure are
all concrete declarations.  Arithmetization, representability, and the
incompleteness theorems are intentionally left for later chains.
-/

namespace FormalOLP.Incompleteness

open FirstOrder

/-! ## The language of Robinson arithmetic -/

inductive QFunction : ℕ → Type
  | zero : QFunction 0
  | succ : QFunction 1
  | add : QFunction 2
  | mul : QFunction 2
  deriving DecidableEq

def QLanguage : Language where
  Functions := QFunction
  Relations := fun _ => Empty

abbrev QTerm (n : ℕ) := QLanguage.Term (Empty ⊕ Fin n)

abbrev QBounded (n : ℕ) := QLanguage.BoundedFormula Empty n

def qvar {n : ℕ} (i : Fin n) : QTerm n :=
  .var (.inr i)

def qzero {n : ℕ} : QTerm n :=
  .func QFunction.zero Fin.elim0

def qsucc {n : ℕ} (t : QTerm n) : QTerm n :=
  .func QFunction.succ ![t]

def qadd {n : ℕ} (t₁ t₂ : QTerm n) : QTerm n :=
  .func QFunction.add ![t₁, t₂]

def qmul {n : ℕ} (t₁ t₂ : QTerm n) : QTerm n :=
  .func QFunction.mul ![t₁, t₂]

def qeq {n : ℕ} (t₁ t₂ : QTerm n) : QBounded n :=
  .equal t₁ t₂

def qneq {n : ℕ} (t₁ t₂ : QTerm n) : QBounded n :=
  (qeq t₁ t₂).not

/-! ## The seven axioms -/

def qAxiom₁ : QLanguage.Sentence :=
  (qneq (qsucc (qvar (0 : Fin 1))) qzero).alls

def qAxiom₂ : QLanguage.Sentence :=
  ((qeq (qsucc (qvar (0 : Fin 2))) (qsucc (qvar (1 : Fin 2)))).imp
      (qeq (qvar (0 : Fin 2)) (qvar (1 : Fin 2)))).alls

def qAxiom₃ : QLanguage.Sentence :=
  ((qneq (qvar (0 : Fin 1)) qzero).imp
      (qeq (qsucc (qvar (1 : Fin 2))) (qvar (0 : Fin 2))).ex).alls

def qAxiom₄ : QLanguage.Sentence :=
  (qeq (qadd (qvar (0 : Fin 1)) qzero) (qvar (0 : Fin 1))).alls

def qAxiom₅ : QLanguage.Sentence :=
  (qeq (qadd (qvar (0 : Fin 2)) (qsucc (qvar (1 : Fin 2))))
      (qsucc (qadd (qvar (0 : Fin 2)) (qvar (1 : Fin 2))))).alls

def qAxiom₆ : QLanguage.Sentence :=
  (qeq (qmul (qvar (0 : Fin 1)) qzero) qzero).alls

def qAxiom₇ : QLanguage.Sentence :=
  (qeq (qmul (qvar (0 : Fin 2)) (qsucc (qvar (1 : Fin 2))))
      (qadd (qmul (qvar (0 : Fin 2)) (qvar (1 : Fin 2))) (qvar (0 : Fin 2)))).alls

/-- Robinson arithmetic as a set of the seven displayed sentences. -/
def robinsonQ : QLanguage.Theory :=
  {qAxiom₁, qAxiom₂, qAxiom₃, qAxiom₄, qAxiom₅, qAxiom₆, qAxiom₇}

theorem qAxiom₁_mem : qAxiom₁ ∈ robinsonQ := by
  simp [robinsonQ]

theorem qAxiom₂_mem : qAxiom₂ ∈ robinsonQ := by
  simp [robinsonQ]

theorem qAxiom₃_mem : qAxiom₃ ∈ robinsonQ := by
  simp [robinsonQ]

theorem qAxiom₄_mem : qAxiom₄ ∈ robinsonQ := by
  simp [robinsonQ]

theorem qAxiom₅_mem : qAxiom₅ ∈ robinsonQ := by
  simp [robinsonQ]

theorem qAxiom₆_mem : qAxiom₆ ∈ robinsonQ := by
  simp [robinsonQ]

theorem qAxiom₇_mem : qAxiom₇ ∈ robinsonQ := by
  simp [robinsonQ]

/-! ## The standard natural-number model -/

@[instance_reducible] def standardNatStructure : QLanguage.Structure ℕ where
  funMap := fun {_n} f v =>
    match f with
    | QFunction.zero => 0
    | QFunction.succ => Nat.succ (v 0)
    | QFunction.add => v 0 + v 1
    | QFunction.mul => v 0 * v 1
  RelMap := fun {_} r _ => nomatch r

attribute [instance] standardNatStructure

@[simp] theorem standardNat_funMap_zero (v : Fin 0 → ℕ) :
    @Language.Structure.funMap QLanguage ℕ standardNatStructure 0 QFunction.zero v = 0 :=
  rfl

@[simp] theorem standardNat_funMap_succ (v : Fin 1 → ℕ) :
    @Language.Structure.funMap QLanguage ℕ standardNatStructure 1 QFunction.succ v = Nat.succ (v 0) :=
  rfl

@[simp] theorem standardNat_funMap_add (v : Fin 2 → ℕ) :
    @Language.Structure.funMap QLanguage ℕ standardNatStructure 2 QFunction.add v = v 0 + v 1 :=
  rfl

@[simp] theorem standardNat_funMap_mul (v : Fin 2 → ℕ) :
    @Language.Structure.funMap QLanguage ℕ standardNatStructure 2 QFunction.mul v = v 0 * v 1 :=
  rfl

theorem standardNat_qAxiom₁ : @Language.Sentence.Realize QLanguage ℕ
    standardNatStructure qAxiom₁ := by
  change ((qneq (qsucc (qvar (0 : Fin 1))) qzero).alls).Realize
    (default : Empty → ℕ)
  rw [Language.BoundedFormula.realize_alls]
  intro xs
  simp [qneq, qeq, qsucc, qzero, qvar,
    Language.BoundedFormula.Realize, Language.Term.realize]

theorem standardNat_qAxiom₂ : @Language.Sentence.Realize QLanguage ℕ
    standardNatStructure qAxiom₂ := by
  change ((qeq (qsucc (qvar (0 : Fin 2))) (qsucc (qvar (1 : Fin 2)))).imp
      (qeq (qvar (0 : Fin 2)) (qvar (1 : Fin 2)))).alls.Realize
    (default : Empty → ℕ)
  rw [Language.BoundedFormula.realize_alls]
  intro xs
  simp_all [qeq, qsucc, qvar, Language.BoundedFormula.Realize, Language.Term.realize]

theorem standardNat_qAxiom₃ : @Language.Sentence.Realize QLanguage ℕ
    standardNatStructure qAxiom₃ := by
  change ((qneq (qvar (0 : Fin 1)) qzero).imp
      (qeq (qsucc (qvar (1 : Fin 2))) (qvar (0 : Fin 2))).ex).alls.Realize
    (default : Empty → ℕ)
  rw [Language.BoundedFormula.realize_alls]
  intro xs
  change (qneq (qvar (0 : Fin 1)) qzero).Realize default xs →
    (qeq (qsucc (qvar (1 : Fin 2))) (qvar (0 : Fin 2))).ex.Realize default xs
  rw [Language.BoundedFormula.realize_ex]
  intro hne
  simp [qneq, qeq, qsucc, qzero, qvar, Language.BoundedFormula.Realize,
    Language.Term.realize] at hne ⊢
  cases hx : xs 0 with
  | zero => exact False.elim (hne hx)
  | succ x => exact ⟨x, by simp [Fin.snoc]⟩

theorem standardNat_qAxiom₄ : @Language.Sentence.Realize QLanguage ℕ
    standardNatStructure qAxiom₄ := by
  change (qeq (qadd (qvar (0 : Fin 1)) qzero) (qvar (0 : Fin 1))).alls.Realize
    (default : Empty → ℕ)
  rw [Language.BoundedFormula.realize_alls]
  intro xs
  simp [qeq, qadd, qvar, qzero, Language.BoundedFormula.Realize,
    Language.Term.realize]

theorem standardNat_qAxiom₅ : @Language.Sentence.Realize QLanguage ℕ
    standardNatStructure qAxiom₅ := by
  change (qeq (qadd (qvar (0 : Fin 2)) (qsucc (qvar (1 : Fin 2))))
      (qsucc (qadd (qvar (0 : Fin 2)) (qvar (1 : Fin 2))))).alls.Realize
    (default : Empty → ℕ)
  rw [Language.BoundedFormula.realize_alls]
  intro xs
  simp [qeq, qadd, qsucc, qvar, Language.BoundedFormula.Realize,
    Language.Term.realize, Nat.add_assoc]

theorem standardNat_qAxiom₆ : @Language.Sentence.Realize QLanguage ℕ
    standardNatStructure qAxiom₆ := by
  change (qeq (qmul (qvar (0 : Fin 1)) qzero) qzero).alls.Realize
    (default : Empty → ℕ)
  rw [Language.BoundedFormula.realize_alls]
  intro xs
  simp [qeq, qmul, qvar, qzero, Language.BoundedFormula.Realize,
    Language.Term.realize]

theorem standardNat_qAxiom₇ : @Language.Sentence.Realize QLanguage ℕ
    standardNatStructure qAxiom₇ := by
  change (qeq (qmul (qvar (0 : Fin 2)) (qsucc (qvar (1 : Fin 2))))
      (qadd (qmul (qvar (0 : Fin 2)) (qvar (1 : Fin 2))) (qvar (0 : Fin 2)))).alls.Realize
    (default : Empty → ℕ)
  rw [Language.BoundedFormula.realize_alls]
  intro xs
  simp [qeq, qadd, qmul, qsucc, qvar, Language.BoundedFormula.Realize,
    Language.Term.realize, Nat.mul_succ]

theorem standardNatModel : @Language.Theory.Model QLanguage ℕ
    standardNatStructure robinsonQ := by
  constructor
  intro φ hφ
  simp only [robinsonQ, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact standardNat_qAxiom₁
  · exact standardNat_qAxiom₂
  · exact standardNat_qAxiom₃
  · exact standardNat_qAxiom₄
  · exact standardNat_qAxiom₅
  · exact standardNat_qAxiom₆
  · exact standardNat_qAxiom₇

theorem robinsonQ_isSatisfiable : robinsonQ.IsSatisfiable := by
  exact @Language.Theory.Model.isSatisfiable QLanguage robinsonQ ℕ
    inferInstance standardNatStructure standardNatModel

end FormalOLP.Incompleteness
