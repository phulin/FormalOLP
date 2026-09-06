import FormalOLP.Computability.RelativeComputability
import Mathlib.Computability.Reduce

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

/-!
## Many-one reductions of sets

The native Mathlib relation `ManyOneReducible` is specialized here to subsets of
`ℕ`.  This keeps the witness visible: a reduction consists of a computable map
and a proof that it preserves membership.  The implication to oracle
reducibility below is deliberately one-way; no equivalence with the
`RecursiveIn` model is assumed.
-/

/-- A computable many-one reduction between sets of natural numbers. -/
abbrev setManyOneReducible (A B : Set ℕ) : Prop :=
  ManyOneReducible (fun n => n ∈ A) (fun n => n ∈ B)

theorem setManyOneReducible_refl (A : Set ℕ) : setManyOneReducible A A := by
  exact manyOneReducible_refl _

theorem setManyOneReducible_trans {A B C : Set ℕ}
    (hAB : setManyOneReducible A B) (hBC : setManyOneReducible B C) :
    setManyOneReducible A C := by
  exact ManyOneReducible.trans hAB hBC

/-!
The following form of transitivity records the composed computable witness
explicitly.  It is useful when a later theorem needs to inspect the map rather
than only use the reducibility proposition.
-/

theorem setManyOneReducible_compose {A B C : Set ℕ} {u v : ℕ → ℕ}
    (hu : Computable u) (hv : Computable v)
    (hAB : ∀ n, n ∈ A ↔ u n ∈ B)
    (hBC : ∀ n, n ∈ B ↔ v n ∈ C) :
    setManyOneReducible A C := by
  refine ⟨v ∘ u, hv.comp hu, ?_⟩
  intro n
  rw [Function.comp_apply]
  exact (hAB n).trans (hBC (u n))

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

/-!
## Many-one reductions give oracle reductions

The proof composes the oracle with the computable witness inside the explicit
`RecursiveIn` constructors.  This establishes the expected soundness
direction without identifying the two machine models.
-/

theorem setManyOneReducible_to_setTuringReducible {A B : Set ℕ}
    (hAB : setManyOneReducible A B) : setTuringReducible A B := by
  rcases hAB with ⟨u, hu, hmem⟩
  have huNat : Nat.Partrec (u : ℕ →. ℕ) := Partrec.nat_iff.1 hu.partrec
  let hu' : RecursiveIn {setCharacteristic B} (fun n => Part.some (u n)) :=
    recursiveIn_of_partrec huNat
  let hB : RecursiveIn {setCharacteristic B} (setCharacteristic B) :=
    RecursiveIn.oracle _ (by simp)
  have hcomp' : RecursiveIn {setCharacteristic B}
      (fun n => Part.some (u n) >>= fun k => setCharacteristic B k) := by
    exact RecursiveIn.comp hB hu'
  have hcomp : RecursiveIn {setCharacteristic B}
      (fun n => setCharacteristic B (u n)) := by
    exact RecursiveIn.of_eq hcomp' (fun n => by simp)
  refine RecursiveIn.of_eq hcomp ?_
  intro n
  simp only [setCharacteristic]
  congr 1
  by_cases hn : n ∈ A
  · simp [hn, (hmem n).mp hn]
  · simp [hn, (hmem n).not.mp hn]

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
