import FormalOLP.Computability.RelativeComputability

/-!
# Turing reducibility

This file formalizes the first reducibility chain from the Open Logic
computability chapter.  The underlying oracle-computation construction is
reused from the staged Lean Pool oracle model; the definitions and theorems
below form the FormalOLP-facing API.

Source correspondence: Lean Pool `Computability/TuringDegree.lean`,
declarations `TuringReducible`, `TuringEquivalent`, and their reflexivity,
transitivity, and equivalence lemmas.  The statements are reproduced here
under the FormalOLP namespace rather than exported through the source
namespace.
-/

namespace FormalOLP.Computability

variable {f g h : ℕ →. ℕ}

/-- `f` is computable with oracle access to `g`. -/
abbrev turingReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

/-- Two partial functions compute one another with oracle access. -/
abbrev turingEquivalent (f g : ℕ →. ℕ) : Prop :=
  turingReducible f g ∧ turingReducible g f

theorem turingReducible_refl (f : ℕ →. ℕ) : turingReducible f f := by
  exact RecursiveIn.oracle f (by simp)

theorem turingReducible_trans (hg : turingReducible f g)
    (hh : turingReducible g h) : turingReducible f h := by
  induction hg with
  | zero | succ | left | right => constructor
  | oracle g' hg => rw [hg]; exact hh
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

theorem turingEquivalent_refl (f : ℕ →. ℕ) : turingEquivalent f f :=
  ⟨turingReducible_refl f, turingReducible_refl f⟩

theorem turingEquivalent_symm (h : turingEquivalent f g) :
    turingEquivalent g f := ⟨h.2, h.1⟩

theorem turingEquivalent_trans (h₁ : turingEquivalent f g)
    (h₂ : turingEquivalent g h) : turingEquivalent f h :=
  ⟨turingReducible_trans h₁.1 h₂.1, turingReducible_trans h₂.2 h₁.2⟩

theorem turingEquivalent_equivalence : Equivalence turingEquivalent where
  refl := turingEquivalent_refl
  symm := turingEquivalent_symm
  trans := turingEquivalent_trans

/-- The total characteristic oracle used to view a set as a Boolean oracle. -/
noncomputable def setCharacteristic (s : Set ℕ) : ℕ →. ℕ := by
  classical
  exact fun n => Part.some (if n ∈ s then 1 else 0)

@[simp] theorem setCharacteristic_mem {s : Set ℕ} {n : ℕ} (hn : n ∈ s) :
    setCharacteristic s n = Part.some 1 := by
  simp [setCharacteristic, hn]

@[simp] theorem setCharacteristic_not_mem {s : Set ℕ} {n : ℕ} (hn : n ∉ s) :
    setCharacteristic s n = Part.some 0 := by
  simp [setCharacteristic, hn]

/-- Set reducibility through characteristic-function oracles. -/
abbrev setTuringReducible (A B : Set ℕ) : Prop :=
  turingReducible (setCharacteristic A) (setCharacteristic B)

theorem setTuringReducible_refl (A : Set ℕ) : setTuringReducible A A :=
  turingReducible_refl _

theorem setTuringReducible_trans {A B C : Set ℕ}
    (hAB : setTuringReducible A B) (hBC : setTuringReducible B C) :
    setTuringReducible A C :=
  turingReducible_trans hAB hBC

abbrev setTuringEquivalent (A B : Set ℕ) : Prop :=
  setTuringReducible A B ∧ setTuringReducible B A

theorem setTuringEquivalent_refl (A : Set ℕ) : setTuringEquivalent A A :=
  ⟨setTuringReducible_refl A, setTuringReducible_refl A⟩

theorem setTuringEquivalent_symm {A B : Set ℕ} (h : setTuringEquivalent A B) :
    setTuringEquivalent B A :=
  ⟨h.2, h.1⟩

theorem setTuringEquivalent_trans {A B C : Set ℕ}
    (hAB : setTuringEquivalent A B) (hBC : setTuringEquivalent B C) :
    setTuringEquivalent A C :=
  ⟨setTuringReducible_trans hAB.1 hBC.1,
    setTuringReducible_trans hBC.2 hAB.2⟩

theorem setTuringEquivalent_equivalence : Equivalence setTuringEquivalent where
  refl := setTuringEquivalent_refl
  symm := setTuringEquivalent_symm
  trans := setTuringEquivalent_trans

end FormalOLP.Computability
