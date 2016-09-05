/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Examples from the tutorial.
-/
import .auto
open tactic

section
variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by safe'
example : p ∨ q ↔ q ∨ p := by safe'

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by safe'
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by safe'

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by safe'
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by safe'

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by safe'
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by safe'
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by safe'
example : ¬p ∨ ¬q → ¬(p ∧ q) := by safe'
example : ¬(p ∧ ¬ p) := by safe'
example : p ∧ ¬q → ¬(p → q) := by safe'
example : ¬p → (p → q) := by safe'
example : (¬p ∨ q) → (p → q) := by safe'
example : p ∨ false ↔ p := by safe'
example : p ∧ false ↔ false := by safe'
example : ¬(p ↔ ¬p) := by safe'
example : (p → q) → (¬q → ¬p) := by safe'

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by safe'
example : ¬(p ∧ q) → ¬p ∨ ¬q := by safe'
example : ¬(p → q) → p ∧ ¬q := by safe'
example : (p → q) → (¬p ∨ q) := by safe'
example : (¬q → ¬p) → (p → q) := by safe'
example : p ∨ ¬p := by safe'
example : (((p → q) → p) → p) := by safe'
end

/- to get the ones that are sorried, we need to find an element in the environment
   to instantiate a metavariable -/

section

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

example : (∃ x : A, r) → r := by auto'
--example : r → (∃ x : A, r) := by auto'
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by auto'

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by auto'

example (h : ∀ x, ¬ ¬ p x) : p a := by force'
example (h : ∀ x, ¬ ¬ p x) : ∀ x, p x := by auto'

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by auto'

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by auto'
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry
example : (∃ x, ¬ p x) → (¬ ∀ x, p x) := by auto'

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by auto'
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

example : (∃ x, p x → r) → (∀ x, p x) → r := by auto'
example : (∃ x, r → p x) → (r → ∃ x, p x) := by auto'

end
