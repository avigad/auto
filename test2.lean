/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Nathaniel Thomas

More examples to test the tableau provers, stolen shamelessly by Jeremy from Nathaniel's "tauto".

Notes: Most things using "safe" (a classical prover) could also use "iauto" (intuitionistic), but
in some cases we need to add more rules to reduce backtracking.

The tableau provers do not currently do much with equality (short of calling them with an "s" in
front for using the simplifier), but we can do more here.
-/
import .auto
open tactic nat

section

variables (a b c d e f : Prop)
variable even : ℕ → Prop
variable P : ℕ → Prop

-- these next five are things that tauto doesn't get

example : (∀ x, P x) ∧ b → (∀ y, P y) ∧ P 0 ∨ b ∧ P 0 := by iauto'
example : (∀ A, A ∨ ¬A) → ∀ x y : ℕ, x = y ∨ x ≠ y := by iauto'
example : ∀ b1 b2, b1 = b2 ↔ (b1 = tt ↔ b2 = tt) := sorry    -- we can't do this either w/o cases
example : ∀ (P Q : nat → Prop), (∀ n, Q n → P n) → (∀ n, Q n) → P 2 := by iauto'
example (a b c : Prop) : ¬ true ∨ false ∨ b ↔ b := by safe'

example : true := by clarify'

example : false → a := by clarify'
example : a → a := by clarify'
example : (a → b) → a → b := by iauto'
example : ¬ a → ¬ a := by clarify'
example : a → (false ∨ a) := by iauto'
example : (a → b → c) → (a → b) → a → c := by iauto'
example : a → ¬ a → (a → b) → (a ∨ b) → (a ∧ b) → a → false := by iauto'
example : ((a ∧ b) ∧ c) → b := by iauto'
example : ((a → b) → c) → b → c := by iauto'
example : (a ∨ b) → (b ∨ a) := by iauto'
example : (a → b ∧ c) → (a → b) ∨ (a → c) := by iauto'
example : ∀ (x0 : a ∨ b) (x1 : b ∧ c), a → b := by iauto'
example : a → b → (c ∨ b) := by iauto'
example : (a ∧ b → c) → b → a → c := by iauto'
example : (a ∨ b → c) → a → c := by iauto'
example : (a ∨ b → c) → b → c := by iauto'
example : (a ∧ b) → (b ∧ a) := by iauto'
example : (a ↔ b) → a → b := by safe'
example : a → ¬¬a := by safe'
example : ¬¬(a ∨ ¬a) := by safe'
example : ¬¬(a ∨ b → a ∨ b) := by safe'
example : ¬¬((∀ n, even n) ∨ ¬(∀ m, even m)) := by auto'
example : (¬¬b → b) → (a → b) → ¬¬a → b := by safe'
example : (¬¬b → b) → (¬b → ¬ a) → ¬¬a → b := by safe'

example : ((a → b → false) → false) → (b → false) → false := by auto'

example : ((((c → false) → a) → ((b → false) → a) → false) → false) →
            (((c → b → false) → false) → false) → ¬a → a := by safe'
example (p q r : Prop) (a b : nat) : true → a = a → q → q → p → p := by safe'
example : ∀ (F F' : Prop), F ∧ F' → F := by safe'
example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 := by safe'
example : ∀ (f : nat → Prop), f 2 → ∃ x, f x := by auto'
example : true ∧ true ∧ true ∧ true ∧ true ∧ true ∧ true := by safe'
example : ∀ (P : nat → Prop), P 0 → (P 0 → P 1) → (P 1 → P 2) → (P 2) := by safe'
example : ¬¬¬¬¬a → ¬¬¬¬¬¬¬¬a → false := by safe'
example : ∀ n, ¬¬(even n ∨ ¬even n) := by safe'
example : ∀ (p q r s : Prop) (a b : nat), r ∨ s → p ∨ q → a = b → q ∨ p := by safe'
example : (∀ x, P x) → (∀ y, P y) := by auto'

example : ((a ↔ b) → (b ↔ c)) → ((b ↔ c) → (c ↔ a)) → ((c ↔ a) → (a ↔ b)) → (a ↔ b) := by safe'

example : ((¬a ∨ b) ∧ (¬b ∨ b) ∧ (¬a ∨ ¬b) ∧ (¬b ∨ ¬b) → false) → ¬((a → b) → b) → false := by safe'

example : ¬((a → b) → b) → ((¬b ∨ ¬b) ∧ (¬b ∨ ¬a) ∧ (b ∨ ¬b) ∧ (b ∨ ¬a) → false) → false := by safe'
example : (¬a ↔ b) → (¬b ↔ a) → (¬¬a ↔ a) := by safe'

example : (¬ a ↔ b) → (¬ (c ∨ e) ↔ d ∧ f) → (¬ (c ∨ a ∨ e) ↔ d ∧ b ∧ f) := by safe'

example {A : Type} (p q : A → Prop) (a b : A) : q a → p b → ∃ x, (p x ∧ x = b) ∨ q x := by auto'

-- for this, we need to make the backtracking search use reflexivity
example {A : Type} (p q : A → Prop) (a b : A) : p b → ∃ x, q x ∨ (p x ∧ x = b) := sorry

example : ¬ a → b → a → c := by safe'
example : a → b → b → ¬ a → c := by safe'
example (a b : nat) : a = b → b = a := by ssafe'

-- good examples of things we don't get, even using the simplifier
example (a b c : nat) : a = b → a = c → b = c := sorry
example (p : nat → Prop) (a b c : nat) : a = b → a = c → p b → p c := sorry

example (p : Prop) (a b : nat) : a = b → p → p := by safe'

-- safe should look for contradictions with constructors
example (a : nat) : (0 : ℕ) = succ a → a = a → false := sorry
example (p : Prop) (a b c : nat) : [a, b, c] = [] → p := sorry

example (a b c : nat) : succ (succ a) = succ (succ b) → c = c := by ssafe'
example (p : Prop) (a b : nat) : a = b → b ≠ a → p := by strong_simp
example : (a ↔ b) → ((b ↔ a) ↔ (a ↔ b)) := by safe'
example (a b c : nat) : b = c → (a = b ↔ c = a) := by ssafe'
example : ¬¬¬¬¬¬¬¬a → ¬¬¬¬¬a → false := by safe'
example (a b c : Prop) : a ∧ b ∧ c ↔ c ∧ b ∧ a := by safe'
example (a b c : Prop) : a ∧ false ∧ c ↔ false := by safe'
example (a b c : Prop) : a ∨ false ∨ b ↔ b ∨ a := by safe'
example : a ∧ not a ↔ false := by safe'
example : a ∧ b ∧ true → b ∧ a := by safe'
example (A : Type) (a₁ a₂ : A) : a₁ = a₂ →
  (λ (B : Type) (f : A → B), f a₁) = (λ (B : Type) (f : A → B), f a₂) := by strong_simp
example (a : nat) : ¬ a = a → false := by strong_simp
example (A : Type) (p : Prop) (a b c : A) : a = b → b ≠ a → p := sorry
example (p q r s : Prop) : r ∧ s → p ∧ q → q ∧ p := by safe'
example (p q : Prop) : p ∧ p ∧ q ∧ q → q ∧ p := by safe'
example (p : nat → Prop) (q : nat → nat → Prop) :
  (∃ x y, p x ∧ q x y) → q 0 0 ∧ q 1 1 → (∃ x, p x) := by auto'
example (p q r s : Prop) (a b : nat) : r ∨ s → p ∨ q → a = b → q ∨ p := by safe'
example (p q r : Prop) (a b : nat) : true → a = a → q → q → p → p := by safe'
example (a b : Prop) : a → b → a := by safe'
example (p q : nat → Prop) (a b : nat) : p a → q b → ∃ x, p x := by auto'

-- definition bnot (b : bool) : bool := cond b ff tt

-- these require cases
example : ∀ b1 b2, b1 && b2 = ff ↔ (b1 = ff ∨ b2 = ff) := sorry
example : ∀ b1 b2, b1 && b2 = tt ↔ (b1 = tt ∧ b2 = tt) := sorry
example : ∀ b1 b2, b1 || b2 = ff ↔ (b1 = ff ∧ b2 = ff) := sorry
example : ∀ b1 b2, b1 || b2 = tt ↔ (b1 = tt ∨ b2 = tt) := sorry
example : ∀ b, bnot b = tt ↔ b = ff := sorry
example : ∀ b, bnot b = ff ↔ b = tt := sorry
example : ∀ b c, b = c ↔ ¬ (b = bnot c) := sorry

inductive and3 (a b c : Prop) : Prop
| mk : a → b → c → and3

example (h : and3 a b c) : and3 b c a := sorry

inductive or3 (a b c : Prop) : Prop
| in1 : a → or3
| in2 : b → or3
| in3 : c → or3
example (h : a) : or3 a b c := sorry
example (h : b) : or3 a b c := sorry
example (h : c) : or3 a b c := sorry

variables (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Prop)
-- H first, all pos

example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) : B₄ := by iauto'
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄) : B₃ := by iauto'
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄) : B₂ := by iauto'
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : B₁ := by safe'

example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₃ := by safe'
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₂ := by safe'
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₁ := by safe'

-- H last, all pos
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₄ := by safe'
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₃ := by safe'
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₂ := by safe'
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₁ := by safe'

example (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₃ := by safe'
example (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₂ := by safe'
example (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₁ := by safe'

-- H first, all neg
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) : ¬B₄ := by safe'
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄) : ¬B₃ := by safe'
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄) : ¬B₂ := by safe'
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬B₁ := by safe'

example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₃ := by safe'
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₂ := by safe'
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₁ := by safe'

-- H last, all neg
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₄ := by safe'
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₃ := by safe'
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₂ := by safe'
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₁ := by safe'

example (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₃ := by safe'
example (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₂ := by safe'
example (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₁ := by safe'

section club
variables Scottish RedSocks WearKilt Married GoOutSunday : Prop
lemma NoMember : (¬Scottish → RedSocks) → (WearKilt ∨ ¬RedSocks) → (Married → ¬GoOutSunday) →
                 (GoOutSunday ↔ Scottish) → (WearKilt → Scottish ∧ Married) →
                 (Scottish → WearKilt) → false := by safe'
end club

end
