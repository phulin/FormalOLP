import Mathlib.Data.Set.Lattice.Indexed

/-!
# Sets, relations, and functions

Planned API for the Open Logic Text material on sets, relations, functions,
size, infinity, and elementary arithmetization.  The source part has the
subtopics `sets`, `relations`, `functions`, `size-of-sets`, `arithmetization`,
and `infinite`; the source-to-module map is in `docs/topic-map.md`.

The first proved API below formalizes the textbook's absorption proposition.
It is deliberately stated with Mathlib's `Set` and lattice operations so that
later developments can use it without introducing a second set interface.
-/

namespace FormalOLP.SetsFunctionsRelations

theorem mem_intersection_union_absorption_iff {α : Type*} (s t : Set α)
    (x : α) : x ∈ s ∩ (s ∪ t) ↔ x ∈ s := by
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, Or.inl hx⟩

theorem intersection_union_absorption {α : Type*} (s t : Set α) :
    s ∩ (s ∪ t) = s := by
  apply Set.ext
  intro x
  exact mem_intersection_union_absorption_iff s t x

end FormalOLP.SetsFunctionsRelations
