import Mathlib.Computability.Partrec

/-!
# Relative partial computation

This is the small oracle-computation substrate needed by the FormalOLP
reducibility API.  It is adapted from the Lean Pool
`Computability/Oracle.lean` declarations `RecursiveIn`,
`recursiveIn_of_partrec`, `recursiveIn_mono`, and `RecursiveIn_subst`.
The broader Pool encoding and typed computability API remain outside this
native integration until their textbook statements are selected.
-/

open Primrec Nat.Partrec Part

namespace FormalOLP.Computability

variable {f g h : ℕ →. ℕ}

/-- Partial functions generated from basic recursion schemes and oracle calls. -/
inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

theorem RecursiveIn.of_eq {O : Set (ℕ →. ℕ)} {f g : ℕ →. ℕ}
    (hf : RecursiveIn O f) (H : ∀ n, f n = g n) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf

/-- Every partial recursive function is recursive relative to any oracle set. -/
lemma recursiveIn_of_partrec (pF : Nat.Partrec f) : RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

/-- Relative computability is monotone in the available oracle set. -/
theorem recursiveIn_mono {O₁ O₂ : Set (ℕ →. ℕ)} (hsub : O₁ ⊆ O₂) {g : ℕ →. ℕ} :
    RecursiveIn O₁ g → RecursiveIn O₂ g := by
  intro hg
  induction hg with
  | zero | succ | left | right => constructor
  | oracle g hg => exact RecursiveIn.oracle g (hsub hg)
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

/-- Replace each original oracle by a function recursive in a new oracle set. -/
theorem RecursiveIn.subst {O O' : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : RecursiveIn O f) (hO : ∀ g, g ∈ O → RecursiveIn O' g) :
    RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

end FormalOLP.Computability
