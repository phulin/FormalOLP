import FormalOLP.PropositionalLogic.Semantics

/-!
# Strong Kleene's three-valued logic

The values and truth tables here follow the K3 presentation in
`OpenLogic/content/many-valued-logic/three-valued-logics/kleene.tex`.
The recursive valuation and designated-value clauses follow
`OpenLogic/content/many-valued-logic/syntax-and-semantics/valuations-sat.tex`
and `multiple-designation.tex`.  K3 designates only `trueVal`; no named-term
or alternative formula syntax is introduced.
-/

namespace FormalOLP.ManyValuedLogic

open FormalOLP.PropositionalLogic

/-- The three truth values of strong Kleene logic. -/
inductive K3 where
  | falseVal
  | undef
  | trueVal
  deriving DecidableEq, Repr

namespace K3

/-- Strong Kleene negation. -/
def neg : K3 → K3
  | falseVal => trueVal
  | undef => undef
  | trueVal => falseVal

/-- Strong Kleene conjunction. -/
def and : K3 → K3 → K3
  | falseVal, _ => falseVal
  | _, falseVal => falseVal
  | trueVal, value => value
  | undef, trueVal => undef
  | undef, undef => undef

/-- Strong Kleene disjunction. -/
def or : K3 → K3 → K3
  | trueVal, _ => trueVal
  | _, trueVal => trueVal
  | falseVal, value => value
  | undef, falseVal => undef
  | undef, undef => undef

/-- Implication is defined as strong Kleene `¬φ ∨ ψ`. -/
def imp (value₁ value₂ : K3) : K3 := or (neg value₁) value₂

@[simp] theorem neg_true : neg trueVal = falseVal := rfl
@[simp] theorem neg_false : neg falseVal = trueVal := rfl
@[simp] theorem neg_undef : neg undef = undef := rfl

theorem neg_eq_true_iff {value : K3} : neg value = trueVal ↔ value = falseVal := by
  cases value <;> simp [neg]

theorem neg_eq_false_iff {value : K3} : neg value = falseVal ↔ value = trueVal := by
  cases value <;> simp [neg]

theorem and_eq_true_iff {value₁ value₂ : K3} :
    and value₁ value₂ = trueVal ↔ value₁ = trueVal ∧ value₂ = trueVal := by
  cases value₁ <;> cases value₂ <;> simp [and]

theorem and_eq_false_iff {value₁ value₂ : K3} :
    and value₁ value₂ = falseVal ↔ value₁ = falseVal ∨ value₂ = falseVal := by
  cases value₁ <;> cases value₂ <;> simp [and]

theorem or_eq_true_iff {value₁ value₂ : K3} :
    or value₁ value₂ = trueVal ↔ value₁ = trueVal ∨ value₂ = trueVal := by
  cases value₁ <;> cases value₂ <;> simp [or]

theorem or_eq_false_iff {value₁ value₂ : K3} :
    or value₁ value₂ = falseVal ↔ value₁ = falseVal ∧ value₂ = falseVal := by
  cases value₁ <;> cases value₂ <;> simp [or]

theorem imp_eq_true_iff {value₁ value₂ : K3} :
    imp value₁ value₂ = trueVal ↔ value₁ = falseVal ∨ value₂ = trueVal := by
  rw [imp, or_eq_true_iff, neg_eq_true_iff]

theorem imp_eq_false_iff {value₁ value₂ : K3} :
    imp value₁ value₂ = falseVal ↔ value₁ = trueVal ∧ value₂ = falseVal := by
  rw [imp, or_eq_false_iff, neg_eq_false_iff]

end K3

/-- Recursive strong Kleene evaluation of the shared OLP formula syntax. -/
def evaluate {Atom : Type} (v : Atom → K3) : Formula Atom → K3
  | .atom atom => v atom
  | .falsum => K3.falseVal
  | .and φ ψ => K3.and (evaluate v φ) (evaluate v ψ)
  | .or φ ψ => K3.or (evaluate v φ) (evaluate v ψ)
  | .imp φ ψ => K3.imp (evaluate v φ) (evaluate v ψ)

@[simp] theorem evaluate_atom {Atom : Type} (v : Atom → K3) (atom : Atom) :
    evaluate v (.atom atom) = v atom := rfl

@[simp] theorem evaluate_falsum {Atom : Type} (v : Atom → K3) :
    evaluate v (.falsum : Formula Atom) = K3.falseVal := rfl

@[simp] theorem evaluate_and {Atom : Type} (v : Atom → K3)
    (φ ψ : Formula Atom) :
    evaluate v (.and φ ψ) = K3.and (evaluate v φ) (evaluate v ψ) := rfl

@[simp] theorem evaluate_or {Atom : Type} (v : Atom → K3)
    (φ ψ : Formula Atom) :
    evaluate v (.or φ ψ) = K3.or (evaluate v φ) (evaluate v ψ) := rfl

@[simp] theorem evaluate_imp {Atom : Type} (v : Atom → K3)
    (φ ψ : Formula Atom) :
    evaluate v (.imp φ ψ) = K3.imp (evaluate v φ) (evaluate v ψ) := rfl

/-- K3 designates exactly its true value. -/
def designated (value : K3) : Prop := value = K3.trueVal

theorem designated_iff (value : K3) : designated value ↔ value = K3.trueVal := Iff.rfl

def satisfies {Atom : Type} (v : Atom → K3) (φ : Formula Atom) : Prop :=
  designated (evaluate v φ)

def satisfiesContext {Atom : Type} (v : Atom → K3)
    (Γ : Set (Formula Atom)) : Prop :=
  ∀ ⦃φ⦄, φ ∈ Γ → satisfies v φ

def entails {Atom : Type} (Γ : Set (Formula Atom)) (φ : Formula Atom) : Prop :=
  ∀ v, satisfiesContext v Γ → satisfies v φ

def valid {Atom : Type} (φ : Formula Atom) : Prop := entails (∅ : Set (Formula Atom)) φ

/-- Booleanization of a K3 valuation, used to compare designated K3 truth with
classical truth. -/
def booleanize {Atom : Type} (v : Atom → K3) : Valuation Atom :=
  fun atom => v atom = K3.trueVal

/- The paired statement is needed because the implication table uses both the
true and false cases of each immediate subformula. -/
theorem reflection {Atom : Type} (v : Atom → K3) (φ : Formula Atom) :
    (evaluate v φ = K3.trueVal → Evaluate (booleanize v) φ) ∧
      (evaluate v φ = K3.falseVal → ¬Evaluate (booleanize v) φ) := by
  induction φ with
  | atom atom =>
      constructor
      · intro h
        simpa [evaluate, booleanize] using h
      · intro h hclass
        have impossible : (K3.falseVal : K3) = K3.trueVal := h.symm.trans hclass
        cases impossible
  | falsum =>
      constructor
      · intro h
        simp [evaluate] at h
      · intro _
        simp [Evaluate]
  | and φ ψ ihφ ihψ =>
      constructor
      · intro h
        have hparts : evaluate v φ = K3.trueVal ∧ evaluate v ψ = K3.trueVal :=
          K3.and_eq_true_iff.mp h
        exact ⟨ihφ.1 hparts.1, ihψ.1 hparts.2⟩
      · intro h
        have hparts : evaluate v φ = K3.falseVal ∨ evaluate v ψ = K3.falseVal :=
          K3.and_eq_false_iff.mp h
        intro hclass
        rcases hparts with hφ | hψ
        · exact (ihφ.2 hφ) hclass.1
        · exact (ihψ.2 hψ) hclass.2
  | or φ ψ ihφ ihψ =>
      constructor
      · intro h
        have hparts : evaluate v φ = K3.trueVal ∨ evaluate v ψ = K3.trueVal :=
          K3.or_eq_true_iff.mp h
        rcases hparts with hφ | hψ
        · exact Or.inl (ihφ.1 hφ)
        · exact Or.inr (ihψ.1 hψ)
      · intro h
        have hparts : evaluate v φ = K3.falseVal ∧ evaluate v ψ = K3.falseVal :=
          K3.or_eq_false_iff.mp h
        intro hclass
        rcases hclass with hφ | hψ
        · exact (ihφ.2 hparts.1) hφ
        · exact (ihψ.2 hparts.2) hψ
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro h
        have hparts : evaluate v φ = K3.falseVal ∨ evaluate v ψ = K3.trueVal :=
          K3.imp_eq_true_iff.mp h
        intro hclass
        rcases hparts with hφ | hψ
        · exact False.elim ((ihφ.2 hφ) hclass)
        · exact ihψ.1 hψ
      · intro h
        have hparts : evaluate v φ = K3.trueVal ∧ evaluate v ψ = K3.falseVal :=
          K3.imp_eq_false_iff.mp h
        intro hclass
        exact (ihψ.2 hparts.2) (hclass (ihφ.1 hparts.1))

theorem true_implies_classical {Atom : Type} {v : Atom → K3} {φ : Formula Atom}
    (h : evaluate v φ = K3.trueVal) : Evaluate (booleanize v) φ :=
  (reflection v φ).1 h

theorem false_implies_classical_false {Atom : Type} {v : Atom → K3}
    {φ : Formula Atom} (h : evaluate v φ = K3.falseVal) :
    ¬Evaluate (booleanize v) φ :=
  (reflection v φ).2 h

theorem modus_ponens_designated {Atom : Type} {v : Atom → K3}
    {φ ψ : Formula Atom} (hφ : designated (evaluate v φ))
    (hImp : designated (evaluate v (.imp φ ψ))) :
    designated (evaluate v ψ) := by
  have hφ' : evaluate v φ = K3.trueVal := hφ
  have hImp' : K3.imp (evaluate v φ) (evaluate v ψ) = K3.trueVal := hImp
  have hnotfalse : ¬evaluate v φ = K3.falseVal := by
    intro hfalse
    have impossible : (K3.trueVal : K3) = K3.falseVal := hφ'.symm.trans hfalse
    cases impossible
  exact (K3.imp_eq_true_iff.mp hImp').resolve_left hnotfalse

theorem k3_valid_implies_classical_valid {Atom : Type} {φ : Formula Atom}
    (h : valid φ) : PropositionalLogic.Tautology φ := by
  intro v hcontext
  classical
  let k3v : Atom → K3 := fun atom => if v atom then K3.trueVal else K3.falseVal
  have hk3 : evaluate k3v φ = K3.trueVal := by
    exact h k3v (by
      intro ψ hψ
      simp at hψ)
  have hbool : booleanize k3v = v := by
    funext atom
    by_cases hatom : v atom <;> simp [booleanize, k3v, hatom]
  have hclass : Evaluate (booleanize k3v) φ := true_implies_classical hk3
  rw [hbool] at hclass
  exact hclass

theorem excluded_middle_not_valid : ¬valid (Formula.or (.atom ()) (Formula.neg (.atom ()))) := by
  intro h
  let v : Unit → K3 := fun _ => K3.undef
  have hv : evaluate v (Formula.or (.atom ()) (Formula.neg (.atom ()))) = K3.undef := by
    simp [evaluate, Formula.neg, K3.imp, K3.or, K3.neg, v]
  have hdesignated : designated (evaluate v
      (Formula.or (.atom ()) (Formula.neg (.atom ())))) := h v (by
        intro ψ hψ
        simp at hψ)
  rw [hv] at hdesignated
  simp [designated] at hdesignated

end FormalOLP.ManyValuedLogic
