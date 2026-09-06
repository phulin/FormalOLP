import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Turing machines

This module gives the Open Logic Project a small, explicit deterministic
Turing-machine interface.  It uses Mathlib's finite-support tape
representation, while keeping the machine alphabet, move/write commands,
configurations, and step relation visible in the FormalOLP namespace.

The machine model is the TM0 model: a transition examines the current state
and scanned symbol, then either halts or chooses a new state together with one
move or write command.  No connection with `RecursiveIn` is asserted here;
that is a separate equivalence theorem requiring additional coding work.
-/

namespace FormalOLP.TuringMachines

abbrev Tape (Γ : Type*) [Inhabited Γ] := Turing.Tape Γ

abbrev Direction := Turing.Dir

/-- A single textbook TM0 action. -/
inductive Instruction (Γ : Type*)
  | move : Direction → Instruction Γ
  | write : Γ → Instruction Γ

instance [Inhabited Γ] : Inhabited (Instruction Γ) :=
  ⟨Instruction.write default⟩

/-- Apply an instruction to the current tape. -/
def Instruction.apply [Inhabited Γ] : Instruction Γ → Tape Γ → Tape Γ
  | .move d, T => Turing.Tape.move d T
  | .write a, T => Turing.Tape.write a T

/-- A deterministic TM0 transition table over a finite alphabet and finite
state set.  The `Inhabited Γ` value is the distinguished blank symbol, while
the `Inhabited Λ` value is the initial state. -/
structure Machine (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where
  transition : Λ → Γ → Option (Λ × Instruction Γ)
  finiteStates : Finite Λ
  finiteAlphabet : Finite Γ

/-- An instantaneous machine configuration. -/
structure Configuration (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where
  state : Λ
  tape : Tape Γ

instance [Inhabited Γ] [Inhabited Λ] : Inhabited (Configuration Γ Λ) :=
  ⟨⟨default, default⟩⟩

namespace Machine

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Execute one machine transition, or return `none` when it halts. -/
def step (M : Machine Γ Λ) (c : Configuration Γ Λ) : Option (Configuration Γ Λ) :=
  (M.transition c.state c.tape.head).map fun (next, instruction) =>
    { state := next, tape := instruction.apply c.tape }

@[simp] theorem step_eq_none_iff (M : Machine Γ Λ) (c : Configuration Γ Λ) :
    M.step c = none ↔ M.transition c.state c.tape.head = none := by
  simp [step]

theorem step_deterministic (M : Machine Γ Λ) {c c₁ c₂ : Configuration Γ Λ}
    (h₁ : M.step c = some c₁) (h₂ : M.step c = some c₂) : c₁ = c₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

@[simp] theorem step_some_iff (M : Machine Γ Λ) (c c' : Configuration Γ Λ) :
    M.step c = some c' ↔
      ∃ next instruction,
        M.transition c.state c.tape.head = some (next, instruction) ∧
          c' = { state := next, tape := instruction.apply c.tape } := by
  constructor
  · intro h
    rcases Option.map_eq_some_iff.mp h with ⟨⟨next, instruction⟩, ht, hcfg⟩
    exact ⟨next, instruction, ht, hcfg.symm⟩
  · rintro ⟨next, instruction, ht, rfl⟩
    simp [step, ht]

end Machine

/-- The one-step transition function, exposed at the topic level. -/
abbrev step {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Configuration Γ Λ) : Option (Configuration Γ Λ) :=
  Machine.step M c

/-- The initial configuration places the input at the head and to its right. -/
def initial {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (input : List Γ) :
    Configuration Γ Λ :=
  { state := default, tape := Turing.Tape.mk₁ input }

/-- A configuration is halted exactly when its transition table returns `none`. -/
def Halted {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Configuration Γ Λ) : Prop := M.step c = none

@[simp] theorem halted_iff_transition_none [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Configuration Γ Λ) :
    Halted M c ↔ M.transition c.state c.tape.head = none :=
  Machine.step_eq_none_iff M c

section Runs

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- A totalized single step.  A halted configuration stays fixed. -/
def totalStep (M : Machine Γ Λ) (c : Configuration Γ Λ) : Configuration Γ Λ :=
  (M.step c).getD c

/-- The deterministic state after exactly `n` totalized steps. -/
def run (M : Machine Γ Λ) (c : Configuration Γ Λ) (n : ℕ) : Configuration Γ Λ :=
  (totalStep M)^[n] c

@[simp] theorem run_zero (M : Machine Γ Λ) (c : Configuration Γ Λ) : run M c 0 = c :=
  rfl

theorem run_succ (M : Machine Γ Λ) (c : Configuration Γ Λ) (n : ℕ) :
    run M c (n + 1) = run M (totalStep M c) n := by
  simp only [run, Function.iterate_succ_apply]

theorem run_succ' (M : Machine Γ Λ) (c : Configuration Γ Λ) (n : ℕ) :
    run M c (n + 1) = totalStep M (run M c n) := by
  simp only [run, Function.iterate_succ_apply']

theorem run_add (M : Machine Γ Λ) (c : Configuration Γ Λ) (m n : ℕ) :
    run M c (m + n) = run M (run M c n) m := by
  exact Function.iterate_add_apply (totalStep M) m n c

@[simp] theorem totalStep_of_halted {M : Machine Γ Λ} {c : Configuration Γ Λ}
    (hc : Halted M c) : totalStep M c = c := by
  rw [totalStep, hc]
  rfl

theorem run_of_halted {M : Machine Γ Λ} {c : Configuration Γ Λ}
    (hc : Halted M c) : ∀ n, run M c n = c
  | 0 => rfl
  | n + 1 => by
      rw [run_succ, totalStep_of_halted hc, run_of_halted hc n]

end Runs

section Computations

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-!
`Computation M c d n` records a finite computation from `c` to `d` using
exactly `n` machine steps.  The successor constructor stores the concrete
`Option` equality for the next step, so the relation is tied to the machine
semantics rather than being an arbitrary transition relation.
-/

inductive Computation (M : Machine Γ Λ) :
    Configuration Γ Λ → Configuration Γ Λ → ℕ → Prop
  | zero (c : Configuration Γ Λ) : Computation M c c 0
  | succ {c c' d : Configuration Γ Λ} {n : ℕ}
      (hstep : M.step c = some c') (hrest : Computation M c' d n) :
      Computation M c d (n + 1)

/-- Topic-level name emphasizing that `Computation` is finite and length-indexed. -/
abbrev FiniteComputation {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c d : Configuration Γ Λ) (n : ℕ) : Prop :=
  Computation M c d n

theorem Computation.run_eq {M : Machine Γ Λ} {c d : Configuration Γ Λ} {n : ℕ}
    (h : Computation M c d n) : run M c n = d := by
  induction h with
  | zero => rfl
  | @succ c c' d n hstep hrest ih =>
      have htotal : totalStep M c = c' := by
        simp [totalStep, hstep]
      rw [run_succ, htotal, ih]

/-!
The converse needs an explicit no-halting hypothesis.  Without it, a
totalized run can stay at a halted configuration for arbitrarily many
iterations, while `Computation` correctly refuses to count those iterations
as successful machine steps.
-/

theorem Computation.of_run {M : Machine Γ Λ} {c : Configuration Γ Λ} {n : ℕ}
    (hnohalt : ∀ k < n, ¬ Halted M (run M c k)) :
    Computation M c (run M c n) n := by
  induction n generalizing c with
  | zero => exact Computation.zero c
  | succ n ih =>
      have hc : ¬Halted M c := by
        intro hhalt
        exact hnohalt 0 (Nat.zero_lt_succ n) hhalt
      have hstep_none : M.step c ≠ none := by
        intro hnone
        exact hc hnone
      rcases Option.ne_none_iff_exists'.mp hstep_none with ⟨c', hstep⟩
      have htotal : totalStep M c = c' := by
        simp [totalStep, hstep]
      have htail : Computation M c' (run M c' n) n := by
        apply ih
        intro k hk hhalt
        apply hnohalt (k + 1) (Nat.succ_lt_succ hk)
        rw [run_succ, htotal]
        exact hhalt
      have hfull : Computation M c (run M c' n) (n + 1) :=
        Computation.succ hstep htail
      simpa [run_succ, htotal] using hfull

theorem Computation.deterministic {M : Machine Γ Λ}
    {c d₁ d₂ : Configuration Γ Λ} {n : ℕ}
    (h₁ : Computation M c d₁ n) (h₂ : Computation M c d₂ n) : d₁ = d₂ := by
  rw [← h₁.run_eq, h₂.run_eq]

theorem Computation.trans {M : Machine Γ Λ}
    {c d e : Configuration Γ Λ} {n m : ℕ}
    (h₁ : Computation M c d n) (h₂ : Computation M d e m) :
    Computation M c e (n + m) := by
  induction h₁ with
  | zero => simpa using h₂
  | @succ c c' d n hstep hrest ih =>
      have htail : Computation M c' e (n + m) := ih h₂
      have hfull : Computation M c e ((n + m) + 1) :=
        Computation.succ hstep htail
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfull

/-!
For an unrestricted totalized run, the genuine computation can be shorter:
once a machine halts, `run` repeats the halted configuration.  This theorem
records the precise bounded relationship and avoids counting those stutters
as machine steps.
-/

theorem Computation.exists_le_of_run {M : Machine Γ Λ} {c : Configuration Γ Λ}
    {n : ℕ} : ∃ k ≤ n, Computation M c (run M c n) k := by
  induction n generalizing c with
  | zero => exact ⟨0, le_rfl, Computation.zero c⟩
  | succ n ih =>
      rcases ih (c := c) with ⟨k, hk, hcomp⟩
      by_cases hh : Halted M (run M c n)
      · refine ⟨k, hk.trans (Nat.le_succ n), ?_⟩
        simpa [run_succ', totalStep_of_halted hh] using hcomp
      · have hstep_none : M.step (run M c n) ≠ none := by
          intro hnone
          exact hh hnone
        rcases Option.ne_none_iff_exists'.mp hstep_none with ⟨c', hstep⟩
        have hone : Computation M (run M c n) c' 1 := by
          simpa using Computation.succ hstep (Computation.zero c')
        have hfull : Computation M c c' (k + 1) := hcomp.trans hone
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        rw [run_succ', totalStep, hstep]
        exact hfull

theorem run_eq_implies_computation_le {M : Machine Γ Λ} {c d : Configuration Γ Λ}
    {n : ℕ} (h : run M c n = d) : ∃ k ≤ n, Computation M c d k := by
  subst d
  exact Computation.exists_le_of_run

theorem Computation.no_nonzero_of_halted {M : Machine Γ Λ}
    {c d : Configuration Γ Λ} {n : ℕ} (hc : Halted M c)
    (h : Computation M c d (n + 1)) : False := by
  cases h with
  | succ hstep _ =>
      cases hc.symm.trans hstep

theorem Computation.after_halted {M : Machine Γ Λ}
    {c d : Configuration Γ Λ} {n : ℕ}
    (h : Computation M c d n) (hd : Halted M d) :
    ∀ k, run M c (n + k) = d
  | 0 => by simpa using h.run_eq
  | k + 1 => by
      rw [Nat.add_succ, run_succ', Computation.after_halted h hd k,
        totalStep_of_halted hd]

/-- A finite computation is a reachability witness for the machine. -/
def Reaches (M : Machine Γ Λ) (c d : Configuration Γ Λ) : Prop :=
  ∃ n, Computation M c d n

theorem reaches_refl (M : Machine Γ Λ) (c : Configuration Γ Λ) : Reaches M c c :=
  ⟨0, Computation.zero c⟩

theorem reaches_trans {M : Machine Γ Λ} {c d e : Configuration Γ Λ}
    (h₁ : Reaches M c d) (h₂ : Reaches M d e) : Reaches M c e := by
  rcases h₁ with ⟨n, hn⟩
  rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, hn.trans hm⟩

theorem run_reaches (M : Machine Γ Λ) (c : Configuration Γ Λ) (n : ℕ) :
    Reaches M c (run M c n) := by
  rcases Computation.exists_le_of_run (M := M) (c := c) (n := n) with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

theorem run_eq_implies_reaches {M : Machine Γ Λ} {c d : Configuration Γ Λ}
    {n : ℕ} (h : run M c n = d) : Reaches M c d := by
  rcases run_eq_implies_computation_le h with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

theorem Computation.to_reaches {M : Machine Γ Λ}
    {c d : Configuration Γ Λ} {n : ℕ} (h : Computation M c d n) :
    Reaches M c d :=
  ⟨n, h⟩

theorem reaches_run_eq {M : Machine Γ Λ} {c d : Configuration Γ Λ}
    (h : Reaches M c d) : ∃ n, run M c n = d := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, hn.run_eq⟩

end Computations

end FormalOLP.TuringMachines
