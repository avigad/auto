/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Examples to test the tableau provers.
-/
import .auto
open tactic

-- useful for debugging
-- set_option pp.beta false
-- set_option pp.delayed_abstraction true
-- set_option pp.universes true
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

/-
--  Quantifier-free examples
-/

section
variables A B C D : Prop

/- clarify -/

example (H : ¬ A) (H' : A) : C := by clarify'
example (H₁ : A ∧ A ∧ B) (H₂ : A ∧ C ∧ B) : A := by clarify'

/- safe -/

example (H : A) (H₁ : ¬ B) : ¬ (A → B) := by safe'
example : A ∨ B → B ∨ A := by safe'
example : A ∧ B → B ∧ A := by safe'
example (H : A) (H₁ : A → B) (H₂ : B → C) : C := by safe'
example (H₁ : A ∧ B) (H₂ : C ∧ B) : C := by safe'
example (HA : A) (HB : B) (HC : C) (HD : D) : (A ∧ B) ∧ (C ∧ D) := by safe'
example (H₁ : A ∧ B) (H₂ : B ∧ ¬ C) : A ∨ C := by safe'
example : (A → B) ∧ (B → C) → A → C := by safe'
example : (A → B) ∨ (B → A) := by safe'
example : ((A → B) → A) → A := by safe'

/- iauto -/

example (H : A) (H₁ : ¬ B) : ¬ (A → B) := by iauto'
example : ¬ (A ↔ ¬ A) := by iauto'
example (H : A ↔ B) (H₁ : A ∧ B → C) (H₂ : ¬ A ∧ ¬ B → C) : C := by safe'
example (H : A ↔ B) (H₁ : (A ∧ ¬ B) ∨ (¬ A ∧ B)) : C := by safe'
example (H : A → B) (H₁ : A) : B := by iauto'
example (H : A → B) (H₁ : B → C) : A → C := by iauto'
example (H : A → B ∨ C) (H₁ : B → D) (H₂ : C → D) : A → D := by iauto'
example : A ∨ B → B ∨ A := by iauto'

/- using injectivity -/

section
open nat

/- using injectivity -/

example (x y : ℕ) : succ x = succ y → x = y ∨ x = succ y := by safe'
-- example (x y z : ℕ) : succ (succ x) = succ y ∧ y = succ z →
--  y = succ x ∧ succ x = succ z := by ssafe'

end

/-
-- Examples with quantifiers
-/

section
variables (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X)

/- auto -/

example (H : ∀ x, P x → Q x) (H₁ : ∀ x, P x) : Q a := by auto'
example (H : ∀ x, P x → Q x) (H₁ : P a) : Q a := by auto'

/- iauto -/

example (H₁ : P a) (H₂ : P b) : ∃ x, P x := by iauto'
example (H₁ : P a) (H₂ : P b) (H₃ : Q b) : ∃ x, P x ∧ Q x := by iauto'
example (H₁ : P b) (H₂ : Q b) (H₃ : P a) : ∃ x, P x ∧ Q x := by iauto'
example (H : ∀ x, P x → Q x ∧ R x) (a : X) (H₁ : P a) : R a ∧ Q a := by auto'
example (H : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x := by iauto'

-- not valid in dependent type theory!
-- example : ∃ x, ((∃ y, P y) → P x) :=
-- by auto'

-- but this would require more intelligent handling of quantifiers
-- example (H : ∃ x : X, x = x) : ∃ x, ((∃ y, P y) → P x) :=
-- by auto'

example : (∃ x, ∀ y, T x y) → ∀ y, ∃ x, T x y := by iauto'

end

end
