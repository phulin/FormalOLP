import Mathlib.Data.Set.Function

/-!
# Functions between sets

This module contains the first native function chain for the Open Logic Text
sets, relations, and functions material.  The textbook treats a function
`A → B` as having an explicit domain and codomain.  Mathlib represents the
same data with an ambient function and `Set.MapsTo`; `Set.BijOn` combines that
codomain condition with injectivity and surjectivity.  The declarations below
keep the textbook domain/codomain hypotheses visible while proving the
composition and inverse steps directly.

The composition statements adapt the function family in
`LeanPool/ZFLean/Functions.lean` (`IsFunc_of_composition_IsFunc`,
`IsInjective.composition_of_injective`, and
`IsSurjective.composition_of_surjective`) to ordinary Mathlib sets.  The
inverse statements correspond to the left- and right-inverse exercises in
`OpenLogic/content/sets-functions-relations/functions/inverses.tex`.

These are native proofs.  This module deliberately imports no `ZFSet` or
other Lean Pool module; the Pool declarations are proof guidance recorded in
the provenance ledger.
-/

namespace FormalOLP.SetsFunctionsRelations

/- The first step in the function-composition chain: composition preserves the
   explicit codomain condition. -/
theorem composition_mapsTo {α β γ : Type*} {A : Set α} {B : Set β} {C : Set γ}
    {f : α → β} {g : β → γ} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    Set.MapsTo (g ∘ f) A C := by
  intro x hx
  exact hg (hf hx)

/- OLP `functions/composition.tex`, injective-composition exercise; adapted
   from `ZFSet.IsInjective.composition_of_injective`. -/
theorem composition_injOn {α β γ : Type*} {A : Set α} {B : Set β}
    {f : α → β} {g : β → γ} (hf : Set.MapsTo f A B) (hfi : Set.InjOn f A)
    (hgi : Set.InjOn g B) : Set.InjOn (g ∘ f) A := by
  intro x hx y hy hxy
  apply hfi hx hy
  change g (f x) = g (f y) at hxy
  exact hgi (hf hx) (hf hy) hxy

/- OLP `functions/composition.tex`, surjective-composition exercise; adapted
   from `ZFSet.IsSurjective.composition_of_surjective`. -/
theorem composition_surjOn {α β γ : Type*} {A : Set α} {B : Set β} {C : Set γ}
    {f : α → β} {g : β → γ} (hf : Set.SurjOn f A B) (hg : Set.SurjOn g B C) :
    Set.SurjOn (g ∘ f) A C := by
  intro z hz
  obtain ⟨y, hy, hyz⟩ := hg hz
  obtain ⟨x, hx, hxy⟩ := hf hy
  refine ⟨x, hx, ?_⟩
  change g (f x) = z
  rw [hxy, hyz]

/- OLP `functions/function-kinds.tex` and `functions/composition.tex`;
   codomain-preserving bijection composition, adapted from
   `ZFSet.IsBijective.composition_of_bijective`. -/
theorem composition_bijOn {α β γ : Type*} {A : Set α} {B : Set β} {C : Set γ}
    {f : α → β} {g : β → γ} (hf : Set.BijOn f A B) (hg : Set.BijOn g B C) :
    Set.BijOn (g ∘ f) A C := by
  refine ⟨composition_mapsTo hf.mapsTo hg.mapsTo, ?_, ?_⟩
  · exact composition_injOn hf.mapsTo hf.injOn hg.injOn
  · exact composition_surjOn hf.surjOn hg.surjOn

/- OLP `functions/inverses.tex`, the left-inverse exercise. -/
theorem leftInverse_injOn {α β : Type*} {A : Set α} {f : α → β} {g : β → α}
    (hgf : Set.LeftInvOn g f A) : Set.InjOn f A := by
  intro x hx y hy hxy
  calc
    x = g (f x) := (hgf hx).symm
    _ = g (f y) := congrArg g hxy
    _ = y := hgf hy

/- OLP `functions/inverses.tex`, the right-inverse exercise.  `hg` records
   that the inverse has the textbook codomain `A`. -/
theorem rightInverse_surjOn {α β : Type*} {A : Set α} {B : Set β}
    {f : α → β} {g : β → α} (hfg : Set.RightInvOn g f B)
    (hg : Set.MapsTo g B A) : Set.SurjOn f A B := by
  intro y hy
  exact ⟨g y, hg hy, hfg hy⟩

/- OLP `functions/inverses.tex`, inverse implies bijection; this is the
   native set-level bridge used before constructing an inverse of a bijection.
   Both maps-to hypotheses are explicit so the codomains remain faithful to
   the textbook `f : A → B` and `g : B → A` presentation. -/
theorem inverse_bijOn {α β : Type*} {A : Set α} {B : Set β}
    {f : α → β} {g : β → α} (hinv : Set.InvOn g f A B)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B A) : Set.BijOn f A B := by
  refine ⟨hf, leftInverse_injOn hinv.1, ?_⟩
  exact rightInverse_surjOn hinv.2 hg

end FormalOLP.SetsFunctionsRelations
