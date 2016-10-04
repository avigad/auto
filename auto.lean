/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Automated tableaux reasoners, inspired by the ones in Isabelle.

  clarify : applies safe rules only, doesn't split goals
  safe : applies safe rules only, though it may split goals
  auto : applies safe rules, and then does a backtracking search with unsafe rules.

All can be called in classical or intuitionistic mode, and all can use the simplifier as well
to simplify the goal and hypotheses.

To do:

- use attribute manager to keep track of rules
- use tactics to build introduction and elimination rules automatically
- need version of apply that doesn't instantiate metavariables
- bound split depth in safe, backtracking depth in force, and iterations in clarify
- rules should match goal w/ or w/out reduction to whnf (reducible)
- improve tracing output by keeping track of backtracking depth
- provide better error messages when the name of a theorem doesn't exist; for example,
    replace mk_const with mk_const_with_warning (when installing the rule?)
- write a splitter, to help simp
- use a backtracking version of reflexivity
- do more instantiations of quantifiers
- with bintro and belim rules, "num_subgoals" is really "num_branches"
- for intuitionistic logic, add a safe elimination rule for A → B, A, and also for A ∨ B → C,
  and similarly for (∃ x, A x) → C
- in fact, for intuitionistic logic, add the rules for Dyckhoff's LJT
- add safe rules for quantifiers, e.g. ∀ x, P x |- P a

Questions:

- In backtracking search, use better selection of rules, e.g. to chose those with fewest subgoals?
- Should calls to simplifier use clarify as the prover?
- Use more sophisticated handling of quantifiers?
- Should we ever call cases, or induction? Maybe with user hints?
- Better handling of equality? E.g. use symmetry as an elim rule?
- When backtracking, can we intelligently detect that some subgoals can be thrown away?
    For example, in the intuitionistic elim rule for A → B, we may end up not using B.
    The tactic that handles that can detect this.
- Check and remove duplicate hypotheses?

Note: the rules are not complete for intuitionistic propositional logic, which may require
using an elim rule on A → B multiple times.
-/
open expr tactic list nat

universe uₗ

declare_trace auto
set_option trace.auto false

/- logic rules for the tableau prover -/

theorem not_or_of_imp {A B : Prop} (H : A → B) : ¬ A ∨ B :=
or.elim (classical.em A) (λ H', or.inr (H H')) (λ H', or.inl H')

lemma classical_swap {A : Prop} (B : Prop) (H₁ : ¬ A) (H₂ : ¬ B → A) : B :=
classical.by_contradiction (λ H, H₁ (H₂ H))

theorem imp_classical_elim {A B C : Prop} (H : A → B) (H₁ : ¬ A → C) (H₂ : B → C) : C :=
or.elim (not_or_of_imp H) (λ H', H₁ H') (λ H', H₂ H')

theorem imp_intuit_elim {A B C : Prop} (H : A → B) (H₁ : A) (H₂ : B → C) : C :=
H₂ (H H₁)

theorem or_classical_intro {A B : Prop} (H : ¬ A → B) : A ∨ B :=
or.elim (classical.em A) (λ H', or.inl H') (λ H', or.inr (H H'))

theorem iff_elim {A B C : Prop} (H : A ↔ B) (H' : (A → B) → (B → A) → C) : C :=
iff.elim H' H

theorem exists.intro2 {A : Type} {P : A → Prop} (a₁ a₂ : A) (H : P a₁ ∨ P a₂) : ∃ x, P x :=
or.elim H (λ H', exists.intro _ H') (λ H', exists.intro _ H')

theorem forall_elim {A : Type} {P : A → Prop} {C : Prop} (H : ∀ x, P x)
  {y : A} (H' : P y → C) : C :=
H' (H y)

theorem forall_elim2 {A : Type} {P : A → Prop} {C : Prop} (H : ∀ x, P x)
  {y₁ y₂ : A} (H' : P y₁ ∧ P y₂ → C) : C :=
H' (and.intro (H y₁) (H y₂))

theorem not_true_elim {C : Prop} (H : ¬ true) : C := false.elim (H trivial)

theorem not_of_not_or_left {A B : Prop} (H : ¬ (A ∨ B)) : ¬ A := λ H', H (or.inl H')

theorem not_of_not_or_right {A B : Prop} (H : ¬ (A ∨ B)) : ¬ B := λ H', H (or.inr H')

theorem forall_not_of_not_exists {A : Type} {P : A → Prop} (H : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
take x H', H (exists.intro x H')

theorem exists_not_of_not_forall {A : Type} {P : A → Prop} (H : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
classical.by_contradiction
  (assume H' : ¬ ∃ x, ¬ P x,
   H (take x, show P x, from classical.by_contradiction (λ H'', H' (exists.intro x H''))))

theorem not_not_dest {A : Prop} (H : ¬ ¬ A) : A :=
classical.by_contradiction (λ H', H H')

theorem not_not_not_dest {A : Prop} (H : ¬ ¬ ¬ A) : ¬ A :=
λ H', H (λ H'', H'' H')

theorem not_not_of_not_imp {A B : Prop} (H : ¬ (A → B)) : ¬ ¬ A :=
λ H', H (λ H'', absurd H'' H')

theorem of_not_imp {A B : Prop} (H : ¬ (A → B)) : A :=
not_not_dest (not_not_of_not_imp H)

theorem not_of_not_imp {A B : Prop} (H : ¬ (A → B)) : ¬ B :=
λ H', H (λ H'', H')

theorem not_or_not_of_not_and {A B : Prop} (H : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
or.elim (classical.em A)
  (λ HA, or.inr (λ HB, H (and.intro HA HB)))
  (λ HnA, or.inl HnA)

theorem contrapos {A B : Prop} (H : A → B) : ¬ B → ¬ A := λ H₁ H₂, H₁ (H H₂)

theorem not_iff {A B : Prop} (H : ¬ (A ↔ B)) : ¬ ((A → B) ∧ (B → A)) := H

theorem not_of_imp_false {A : Prop} (H : A → false) : ¬ A := H

theorem imp_of_or_imp_left {A B C : Prop} (H : A ∨ B → C) : A → C :=
λ H', H (or.inl H')

theorem imp_of_or_imp_right {A B C : Prop} (H : A ∨ B → C) : B → C :=
λ H', H (or.inr H')


namespace tactic

/- utils -/

meta def collect_props : list expr → tactic (list expr)
| []        := return []
| (h :: hs) := do
  props   ← collect_props hs,
  ht      ← infer_type h,
  htt     ← infer_type ht,
  (unify htt prop >> return (h :: props)) <|> return props

meta def unfold_all (ns : list name) : tactic unit :=
do unfold ns, local_context >>= collect_props >>= monad.mapM' (unfold_at ns)

meta def head_symbol : expr → name
| (const n a)      := n
| (app e a)        := match (get_app_fn e) with
                      | (const n l) := n
                      | a           := `none
                      end
| (pi a₁ a₂ a₃ a₄) := `pi
| a                := `none

private meta def whnf_red : expr → tactic expr := whnf_core reducible

meta def is_forall (e : expr) : tactic bool :=
if head_symbol e ≠ `pi then return ff
   else do
     et ← infer_type e,
     if et ≠ prop then return ff
     else do
       dt ← infer_type (binding_domain e),
       if dt ≠ prop then return tt else return ff

meta def is_negation (e : expr) : tactic bool :=
do e' ← whnf_red e,
   if head_symbol e' = `not then return tt
   else if is_pi e' = tt then
    (do b' ← whnf_red (binding_body e'),
        cond (is_false b')
          (return tt)
          (return ff))
   else return ff

meta def at_least_once (t : tactic unit) : tactic unit :=
t >> repeat t

-- assert_fresh P infers the type T of P, creates a fresh name H, and
--   asserts H : T
meta def assert_fresh (P : expr) : tactic unit :=
do n ← mk_fresh_name,
   t ← infer_type P,
   assertv n t P

meta def expr_with_type_to_string (h : expr) : tactic string :=
do ht ← infer_type h,
   pph ← pp h,
   ppht ← pp ht,
   return (to_string pph ++ " : " ++ to_string ppht)

/- versions of the simplifier that call themselves recursively -/

-- simp_add_prove_max_depth l d uses the simplifier as its own prover, recursing up to depth d
meta def simp_add_prove_max_depth (lemmas : list expr) : ℕ → tactic unit
| 0        := failed
| (succ d) := do l ← local_context >>= collect_props,
                 simplify_goal (simp_add_prove_max_depth d) (l ++ lemmas),
                 triv

meta def strong_simp_add (lemmas : list expr) : tactic unit :=
do l ← local_context >>= collect_props,
   simplify_goal (simp_add_prove_max_depth lemmas 10) (l ++ lemmas),
   try triv

meta def strong_simp : tactic unit :=
strong_simp_add []

meta def strong_simp_at_add (h : expr) (lemmas : list expr) : tactic unit :=
do simp_core_at (simp_add_prove_max_depth lemmas 10) lemmas h

meta def strong_simp_at (h : expr) : tactic unit :=
do strong_simp_at_add h []

-- TODO: how to inline this?
private meta def strong_simp_hyps_add_aux (lemmas : list expr) : list expr → tactic unit
| [] := skip
| (h :: hs) := try (strong_simp_at_add h lemmas) >> strong_simp_hyps_add_aux hs

meta def strong_simp_hyps_add (lemmas : list expr) : tactic unit :=
do l ← local_context,
   strong_simp_hyps_add_aux lemmas l

meta def strong_simp_hyps : tactic unit :=
strong_simp_hyps_add []


/-
  These are for tracing. We use a thunk to avoid computing a string when it is not needed.
-/

-- show a trace message
meta def auto_trace (s : unit → string) : tactic unit :=
if is_trace_enabled_for `auto = tt then trace (s ()) else skip

-- a version where the string is in the tactic monad
meta def auto_traceM (s : unit → tactic string) : tactic unit :=
if is_trace_enabled_for `auto = tt then s () >>= trace else skip

-- trace a step, e.g. an application of a rule, and show the result
meta def auto_trace_step (tac : tactic unit) (s : unit → string) : tactic unit :=
if is_trace_enabled_for `auto = tt then do
  trace (s ()),
  (tac >> trace ("result:") >> trace_state >> trace "-----") <|>
    (trace ("failed:") >> trace_state >> trace "-----" >> failed)
else
  tac

-- a version where the string is in the tactic monad
meta def auto_trace_stepM (tac : tactic unit) (s : unit → tactic string) : tactic unit :=
if is_trace_enabled_for `auto = tt then do
  s () >>= trace,
  (tac >> trace ("result:") >> trace_state >> trace "-----") <|>
      (trace ("failed:") >> trace_state >> trace "-----" >> failed)
else
  tac

-- this can be used to print a message after a tactic if it fails, e.g. a continuation.
meta def auto_trace_with_fail_message (tac : tactic unit) (s : unit → string) :
  tactic unit :=
if is_trace_enabled_for `auto = tt then do
  tac <|> (trace (s ()) >> failed)
else
  tac

meta def auto_trace_with_fail_messageM (tac : tactic unit) (s : unit → tactic string) :
  tactic unit :=
if is_trace_enabled_for `auto = tt then do
  tac <|> (s () >>= trace >> failed)
else
  tac

/-
  Safe versions of some tactics, i.e. tactics that do not instantiate metavariables and
  hence can be applied in safe mode.
-/

-- we really want: e₁ and e₂ can be unified without instantiating metavariables
meta def unify_safe_core (t : transparency) (e₁ e₂ : expr) : tactic unit :=
cond (has_meta_var e₁ || has_meta_var e₂) failed (unify_core t e₁ e₂)

meta def unify_safe (e₁ e₂ : expr) : tactic unit :=
unify_safe_core semireducible e₁ e₂

-- we really want: try to apply e, without instantiation any metavariables in the goal
-- maybe we also want the same for fapply?
meta def apply_safe_core (t : transparency) (all : bool) (insts : bool) (e : expr) :
  tactic unit :=
apply_core t all insts e

meta def apply_safe : expr → tactic unit :=
apply_safe_core semireducible ff tt

/- a safe version of assumption -/

meta def find_same_type_safe (e : expr) (l : list expr) : tactic expr :=
first $ list.for l (λ h, do ht ← infer_type h, unify_safe e ht >> return h)

meta def find_hyp_with_type (e : expr) : tactic expr :=
local_context >>= find_same_type_safe e

meta def assumption_safe : tactic unit :=
do goal ← target,
   h ← find_hyp_with_type goal,
   auto_trace_stepM (exact h)
     (λ u, do s ← expr_with_type_to_string h,
              return ("applying assumption " ++ s))

/- a safe version of contradiction -/

private meta def contra_A_not_A_safe : list expr → list expr → tactic unit
| []         Hs := failed
| (H1 :: Rs) Hs :=
  do t_0 ← infer_type H1,
     t   ← whnf t_0,
     (do a ← match_not t,
         H2 ← find_same_type_safe a Hs,
         tgt ← target,
         pr ← mk_app `absurd [tgt, H2, H1],
         auto_trace_stepM (exact pr)
           (λ u, do s2 ← expr_with_type_to_string H2,
                    s1 ← expr_with_type_to_string H1,
                    return ("using contradiction, " ++ s2 ++ ", " ++ s1)))
         <|> contra_A_not_A_safe Rs Hs

meta def contradiction_safe : tactic unit :=
do ctx ← local_context, contra_A_not_A_safe ctx ctx


/-
The structure storing a rule has the following data:

  key : name         := the head symbol that triggers the rule
  num_subgoals : nat := number of subgoals introduced
  classical : bool   := whether to use in classical mode
  intuit : bool      := whether to use in intuitionistic mode
  tac : ...          := the tactic used to execute the rule

Notice that all the work is done by tac, which is arbitrary. Helper functions build suitable
tactics in common situations, but users can write more complicated ones. All the other data
is used to find the rules quickly and decide when to apply them.

Currently, the only thing that varies is the type of the tactic, so this is given as a parameter:

  intro_rule  == tactic unit
  elim_rule   == expr → tactic unit
  bintro_rule == tactic unit → tactic unit
  belim_rule  == tactic unit → expr → tactic unit

Intro rules are keyed on the head symbol of the goal. Elim rules are keyed on the head symbol of
a hypothesis, and take that hypothesis as an argument. We actually have a separate rule
database for rules where they head symbol is a negation, keyed to the next head symbol.

The intro and elim rules should be safe, which is to say, they can be applied without
backtracking. In the other rules, the letter "b" is for "backtracking." Those rules take
continuations that carry out the rest of the search, so that they can backtrack on failure.

Note that many some elimination rules that would otherwise be safe become unsafe when there are
metavariables involved. For example, applying (or.elim H) is unsafe if H has metavariables; if
those metavariables are not instantiated by the end of the search, then the attempt was
unsuccessful, and needs to be retracted. So there are both safe and unsafe versions of the rule
for or.
-/

structure rule_data (A : Type) :=
(key : name) (num_subgoals : ℕ) (classical : bool) (intuit : bool) (tac : A)

meta def rule_key {A : Type} : rule_data A → name := rule_data.key

meta def intro_rule : Type  := rule_data (tactic unit)
meta def elim_rule : Type   := rule_data (expr → tactic unit)
meta def bintro_rule : Type := rule_data (tactic unit → tactic unit)
meta def belim_rule : Type  := rule_data (expr → tactic unit → tactic unit)

meta def rule_database (A : Type) : Type := rb_lmap name (rule_data A)

meta def intro_rule_database : Type  := rb_lmap name intro_rule
meta def elim_rule_database : Type   := rb_lmap name elim_rule
meta def nelim_rule_database : Type  := rb_lmap name elim_rule
meta def bintro_rule_database : Type := rb_lmap name bintro_rule
meta def belim_rule_database : Type  := rb_lmap name belim_rule
meta def bnelim_rule_database : Type := rb_lmap name belim_rule

meta def mk_rule_database (A : Type) : rule_database A := rb_lmap.mk _ _

meta def insert_rule {A : Type} (db : rule_database A) (r : rule_data A) :
  rule_database A :=
rb_lmap.insert db (rule_key r) r

meta def insert_rule_list {A : Type} (db : rule_database A) :
  list (rule_data A) → rule_database A
| []        := db
| (r :: rs) := insert_rule (insert_rule_list rs) r

meta def initialize_rule_database {A : Type} (l : list (rule_data A)) : rule_database A :=
insert_rule_list (mk_rule_database A) l

meta def find_rules {A : Type} (db : rule_database A) (key : name) : list (rule_data A) :=
rb_lmap.find db key


/- intro rules -/

meta def apply_intro_rule (db : intro_rule_database) (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do goal ← target >>= whnf_red,
   first $ list.for (find_rules db (head_symbol goal))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                 cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             rule_data.tac r
           else failed)

/- procedures for building particular intro rules -/

meta def deploy_intro (op : name) : tactic unit :=
auto_trace_step (mk_const op >>= apply)
                (λ u, "applying introduction " ++ to_string op)

meta def deploy_intro_then_intros (op : name) : tactic unit :=
auto_trace_step (mk_const op >>= apply >> intros >> return ())
                (λ u, "applying introduction " ++ to_string op)


/- elim rules -/

meta def apply_elim_rule_at (edb : elim_rule_database) (nedb : nelim_rule_database)
    (h : expr) (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do ht ← infer_type h >>= whnf_red,
   (first $ list.for (find_rules edb (head_symbol ht))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             rule_data.tac r h
           else failed)) <|>
   if head_symbol ht = `not then do
      unneg ← return (app_arg ht) >>= whnf_red,
      first $ list.for (find_rules nedb (head_symbol (unneg)))
            (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                      cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
                    rule_data.tac r h
                  else failed)
   else failed

meta def apply_elim_rule (edb : elim_rule_database) (nedb : nelim_rule_database)
    (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do hs ← local_context >>= collect_props,
   first $ list.for hs (λ h, apply_elim_rule_at edb nedb h max_subgoals classical)

/- procedures for building particular elim rules

   general elimination rules: All the arguments are assumed to be inferrable from the motive and
     major premise. The rule is not applied if the hypothesis has metavariables -- backtracking
     is needed for that.

   destruct rules: This eliminates a hypothesis by applying a single theorem or a list of
     theorems in the forward direction. The arguments are assume to be inferrable from the premise.
     It is safe even if the hypothesis has variables.
-/

private meta def elim_instance_mapp_args (motive major : ℕ) (emotive emajor : expr) :
  list (option expr) :=
let diff := major - motive in
nat.rec_on major []
  (λ n l, if n = diff then some emotive :: l
          else if n = 0 then some emajor :: l else none :: l)

meta def deploy_elim_at (op : name) (motive : ℕ) (major : ℕ) : expr → tactic unit :=
λ h : expr,
do auto_trace_stepM
     (do goal ← target,
         el ← mk_mapp op (elim_instance_mapp_args motive major goal h),
         clear h,
         apply el ; (intros >> skip),
         return ())
     (λ u, do s ← expr_with_type_to_string h,
              return ("applying elimination " ++ to_string op ++ " at " ++ s))

-- only apply the elim rule if there are no metavars
meta def deploy_elim_at_safe (op : name) (motive : ℕ) (major : ℕ) :
  expr → tactic unit :=
λ h : expr,
do ht ← infer_type h,
   when (has_meta_var ht = tt) failed,
   deploy_elim_at op motive major h

private meta def dest_instance_mapp_args (prem : ℕ) (hyp : expr) :
  list (option expr) :=
nat.rec_on (prem - 1) [some hyp] (λ n l, none :: l)

meta def deploy_dest_at (op : name) (prem : ℕ) : expr → tactic unit :=
λ h : expr,
auto_trace_stepM
  (mk_mapp op (dest_instance_mapp_args prem h) >>= assert_fresh >> clear h)
  (λ u, do s ← expr_with_type_to_string h,
           return ("applying destructor " ++ to_string op ++ " at " ++ s))

meta def deploy_dests_at (ops : list (name × ℕ)) : expr → tactic unit :=
λ h : expr,
auto_trace_stepM
  (monad.forM' ops (λ p, mk_mapp (p.1) (dest_instance_mapp_args (p.2) h) >>= assert_fresh) >>
    clear h)
  (λ u, do s ← expr_with_type_to_string h,
           return ("applying destructors " ++ (map prod.fst ops)^.to_string ++ " at " ++ s))

meta def deploy_clear_at : expr → tactic unit :=
λ h : expr,
auto_trace_stepM (clear h)
  (λ u, do s ← expr_with_type_to_string h,
           return ("clearing " ++ s))

-- convert (... h : ¬ A ... ==> B) to (... hn : ¬ B ... ==> A), where h' has a fresh name
meta def do_classical_swap (h : expr) : tactic expr :=
do goal ← target,
   mk_mapp `classical_swap [none, some goal, some h] >>= apply,
   clear h,
   mk_fresh_name >>= intro

meta def classical_apply_intro_rule_at (db : intro_rule_database) (h : expr)
    (max_subgoals : ℕ) (classical : bool) :
  tactic unit :=
do n ← mk_fresh_name,
   negated_concl ← do_classical_swap h,
   apply_intro_rule db max_subgoals classical ;
     (intros >> do_classical_swap negated_concl >> skip)


/- backtracking intro rules -/

meta def apply_bintro_rule (db : bintro_rule_database) (max_subgoals : ℕ)
    (classical : bool) (cont : tactic unit) :
  tactic unit :=
do goal ← target >>= whnf_red,
   first $ list.for (find_rules db (head_symbol goal))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             rule_data.tac r cont
           else failed)

/- procedure for building particular bintro rules -/

meta def deploy_bintro_choices (l : list (tactic unit)) : tactic unit → tactic unit :=
take cont, first $ list.for l (λ t, do
  auto_trace (λ u, "setting backtracking point for intro rule"),
  t,
  auto_trace_with_fail_message cont (λ u, "backtracking intro rule"))


/- backtracking elim rules -/

meta def classical_apply_bintro_rule_at (db : bintro_rule_database) (h : expr)
    (max_subgoals : ℕ) (classical : bool) (cont : tactic unit) :
  tactic unit :=
do n ← mk_fresh_name,
   negated_concl ← do_classical_swap h,
   apply_bintro_rule db max_subgoals classical (intros >> do_classical_swap negated_concl >> cont)

meta def apply_belim_rule_at (bedb : belim_rule_database) (bnedb : belim_rule_database)
    (h : expr) (max_subgoals : ℕ) (classical : bool) (cont : tactic unit) :
  tactic unit :=
do ht ← infer_type h >>= whnf_red,
   (first $ list.for (find_rules bedb (head_symbol ht))
     (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
             rule_data.tac r h cont
           else failed)) <|>
   (monad.condM (is_negation ht)
     (do dt ← infer_type (binding_domain h),
         first $ list.for (find_rules bnedb (head_symbol dt))
            (λ r, if rule_data.num_subgoals r ≤ max_subgoals ∧
                      cond classical (rule_data.classical r) (rule_data.intuit r) = tt then
                    rule_data.tac r h cont
                  else failed))
     failed)

meta def apply_belim_rule (bedb : belim_rule_database) (bnedb : belim_rule_database)
    (max_subgoals : ℕ) (classical : bool) (cont : tactic unit) :
  tactic unit :=
do hs ← local_context >>= collect_props,
   first (list.for hs (λ h, apply_belim_rule_at bedb bnedb h max_subgoals classical cont))


/- procedure for building particular belim rules -/

meta def deploy_belim_choices (l : list (expr → tactic unit)) :
  expr → tactic unit → tactic unit :=
take h cont,
  (first $ list.for l (λ t, do
    auto_traceM (λ u, do s ← expr_with_type_to_string h,
                         return ("setting backtracking point for elim rule at " ++ s)),
    t h,
    auto_trace_with_fail_messageM cont
      (λ u, do s ← expr_with_type_to_string h,
                         return ("backtracking elim rule at " ++ s))))


/- try to do a subst or injection on a hypothesis -/

meta def has_eq_type (h : expr) : tactic bool :=
do htype ← infer_type h >>= whnf_red,
   return (match (expr.is_eq htype) with (some _) := tt | none := ff end)

meta def try_subst_and_injection_on_hyps : tactic unit :=
do ctx ← local_context,
   first $ list.for ctx (λ h, do
     b ← has_eq_type h,
     when (b = ff) failed,
     (do subst h,
         auto_trace_stepM skip
           (λ u, do s ← expr_with_type_to_string h,
                    return ("performing subst with " ++ s)),
         clear h) <|>
     (do injection h,
         auto_trace_stepM skip
           (λ u, do s ← expr_with_type_to_string h,
                    return ("performing injection with " ++ s)),
        clear h))


/-
    Standard rule sets
-/

/- standard introduction rules -/

meta def true_intro_rule : intro_rule :=
{ key := ``true, num_subgoals := 0, classical := tt, intuit := tt,
    tac := deploy_intro ``true.intro }

meta def and_intro_rule : intro_rule :=
{ key := ``and, num_subgoals := 2, classical := tt, intuit := tt,
    tac := deploy_intro ``and.intro }

meta def or_classical_intro_rule : intro_rule :=
{ key := ``or, num_subgoals := 1, classical := tt, intuit := ff,
    tac := deploy_intro_then_intros ``or_classical_intro }

-- TODO: eliminate trick to get the recursive call
private meta def auto_intros_aux : unit → tactic unit
| unit.star :=
  do goal ← target >>= whnf_red,
     when (head_symbol goal = `pi ∨ head_symbol goal = `not)
       (do n ← mk_fresh_name, intro n, auto_intros_aux unit.star)

meta def auto_intros : tactic unit :=
auto_intros_aux unit.star

meta def deploy_intros : tactic unit :=
auto_trace_step auto_intros (λ u, "applying intros")

meta def Pi_intro_rule : intro_rule :=
{ key := `pi, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_intros }

meta def not_intro_rule : intro_rule :=
{ key := ``not, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_intros }

meta def iff_intro_rule : intro_rule :=
{ key := ``iff, num_subgoals := 2, classical := tt, intuit := tt,
    tac := deploy_intro ``iff.intro }

meta def standard_intro_rules : list intro_rule :=
[true_intro_rule, and_intro_rule, or_classical_intro_rule, Pi_intro_rule, not_intro_rule,
  iff_intro_rule]

/- standard backtracking intro rules -/

meta def or_intuit_bintro_rule : bintro_rule :=
{ key := ``or, num_subgoals := 2, classical := ff, intuit := tt,
    tac := deploy_bintro_choices [deploy_intro ``or.inl, deploy_intro ``or.inr] }

meta def exists_bintro_rule : bintro_rule :=
{ key := ``Exists, num_subgoals := 2, classical := tt, intuit := tt,
    tac := deploy_bintro_choices [deploy_intro ``exists.intro, deploy_intro ``false.elim] }

meta def standard_bintro_rules : list bintro_rule :=
[or_intuit_bintro_rule, exists_bintro_rule]

/- standard elimination rules -/

meta def and_elim_rule : elim_rule :=
{ key := ``and, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_dests_at [(``and.left, 3), (``and.right, 3)] }

meta def iff_elim_rule : elim_rule :=
{ key := ``iff, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_dests_at [(``iff.mp, 3), (``iff.mpr, 3)] }

meta def or_elim_rule : elim_rule :=
{ key := ``or, num_subgoals := 2, classical := tt, intuit := tt,
    tac := deploy_elim_at_safe ``or.elim 3 4 }

meta def false_elim_rule : elim_rule :=
{ key := ``false, num_subgoals := 0, classical := tt, intuit := tt,
    tac := deploy_elim_at ``false.elim 1 2 }

meta def exists_elim_rule : elim_rule :=
{ key := ``Exists, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_elim_at_safe ``exists.elim 3 4 }

-- given a hypothesis h with type ht, an implication, try to find something
-- in the context to apply it to
meta def try_modus_ponens_at (h : expr) (ht : expr) : tactic unit :=
do h' ← find_hyp_with_type (binding_domain ht),
   auto_trace_stepM
     (assert_fresh (expr.app h h') >> clear h)
     (λ u, do s₁ ← expr_with_type_to_string h,
              s₂ ← expr_with_type_to_string h',
              return ("applying " ++ s₁ ++ " to " ++ s₂))

-- if h is of the form A → B:
--   if B = false, replace by h' : ¬ A
--   if h' : A is in the context, apply h to h'
--   if A if of the form C ∨ D, replace with C → B, D → B
meta def deploy_imp_elim_at (h : expr) : tactic unit :=
do ht ← infer_type h >>= whnf_red,
   dt ← infer_type (binding_domain ht),
   if dt ≠ prop then failed
   else do
     conc ← return (binding_body ht) >>= whnf_red,
     if head_symbol conc = ``false then
       deploy_dest_at ``not_of_imp_false 2 h
     else try_modus_ponens_at h ht <|>
            (do hyp ← return (binding_domain ht) >>= whnf_red,
                if head_symbol hyp = `or then
                   deploy_dests_at [(``imp_of_or_imp_left, 4), (``imp_of_or_imp_right, 4)] h
                else failed)

meta def imp_elim_rule : elim_rule :=
{ key := `pi, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_imp_elim_at }

meta def deploy_imp_classical_elim_at (h : expr) : tactic unit :=
do ht ← infer_type h >>= whnf_red,
   dt ← infer_type (binding_domain ht),
   if dt ≠ prop then failed
   else monad.condM (is_negation ht)
     failed
     (deploy_elim_at ``imp_classical_elim 3 4 h)

meta def imp_classical_elim_rule : elim_rule :=
{ key := `pi, num_subgoals := 2, classical := tt, intuit := ff,
    tac := deploy_imp_classical_elim_at }

-- try to find a contradiction
meta def deploy_not_elim_at (h : expr) : tactic unit :=
do ht ← infer_type h,
   h' ← find_hyp_with_type (app_arg ht),
   goal ← target,
   t ← mk_app `absurd [goal, h', h],
   auto_trace_stepM
     (exact t)
     (λ u, do s₁ ← expr_with_type_to_string h',
              s₂ ← expr_with_type_to_string h,
              return ("using contradiction, " ++ s₁ ++ " and " ++ s₂))

meta def not_elim_rule : elim_rule :=
{ key := `not, num_subgoals := 0, classical := tt, intuit := tt,
    tac := deploy_not_elim_at }

meta def standard_elim_rules : list elim_rule :=
[and_elim_rule, or_elim_rule, false_elim_rule, exists_elim_rule, imp_elim_rule,
  imp_classical_elim_rule, not_elim_rule, iff_elim_rule]

/- elimination rules for negated formulas -/

meta def not_true_elim_rule : elim_rule :=
{ key := ``true, num_subgoals := 0, classical := tt, intuit := tt,
    tac := deploy_elim_at ``not_true_elim 1 2 }

meta def not_or_elim_rule : elim_rule :=
{ key := ``or, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_dests_at [(``not_of_not_or_left, 3), (``not_of_not_or_right, 3)] }

meta def not_and_elim_rule : elim_rule :=
{ key := ``and, num_subgoals := 1, classical := tt, intuit := ff,
    tac := deploy_dest_at ``not_or_not_of_not_and 3 }

meta def not_imp_elim_rule : elim_rule :=
{ key := `pi, num_subgoals := 1, classical := tt, intuit := ff,
    tac := deploy_dests_at [(``of_not_imp, 3), (``not_of_not_imp, 3)] }

meta def not_not_elim_rule : elim_rule :=
{ key := ``not, num_subgoals := 1, classical := tt, intuit := ff,
    tac := deploy_dest_at ``not_not_dest 2 }

meta def not_not_not_elim_rule : elim_rule :=
{ key := ``not, num_subgoals := 1, classical := ff, intuit := tt,
    tac := deploy_dest_at ``not_not_not_dest 2 }

meta def not_iff_elim_rule : elim_rule :=
{ key := ``iff, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_dest_at ``not_iff 3 }

meta def not_exists_elim_rule : elim_rule :=
{ key := ``Exists, num_subgoals := 1, classical := tt, intuit := tt,
    tac := deploy_dest_at ``forall_not_of_not_exists 3 }

meta def standard_nelim_rules : list elim_rule :=
[not_true_elim_rule, not_or_elim_rule, not_and_elim_rule, not_imp_elim_rule,
 not_not_elim_rule, not_not_not_elim_rule, not_iff_elim_rule, not_exists_elim_rule]

/- standard backtracking elim rules -/

meta def deploy_imp_intuit_belim_at (h : expr) (cont : tactic unit) : tactic unit :=
do ht ← infer_type h >>= whnf_red,
   dt ← infer_type (binding_domain ht),
   if dt ≠ prop then failed
   else deploy_belim_choices [deploy_elim_at ``imp_intuit_elim 3 4, deploy_clear_at] h cont

meta def imp_intuit_belim_rule : belim_rule :=
{ key := `pi, num_subgoals := 2, classical := ff, intuit := tt,
    tac := deploy_imp_intuit_belim_at }

--meta def imp_classical_belim_rule :=
--{ key := `pi, num_subgoals := 2, classical := tt, intuit := ff,
--    tac := deploy_belim_choices [deploy_clear_at, deploy_imp_classical_elim_at] }

meta def or_belim_rule : belim_rule :=
{ key := `or, num_subgoals := 2, classical := ff, intuit := tt,
    tac := deploy_belim_choices [deploy_clear_at, deploy_elim_at ``or.elim 3 4] }

meta def standard_belim_rules : list belim_rule :=
[imp_intuit_belim_rule, or_belim_rule]

/- standard backtracking negated elim rules -/

meta def standard_bnelim_rules : list belim_rule := []


/- backtracking assumption tactic -/

meta def try_assumptions (cont : tactic unit) :=
do ctx ← local_context,
   goal ← target,
   first $ list.for ctx
     (λ h, do ht ← infer_type h,
              unify ht goal,
              auto_trace_stepM (exact h)
                  (λ u, do s ← expr_with_type_to_string h,
                           return ("try applying assumption " ++ s)),
              auto_trace_with_fail_messageM cont
                  (λ u, do s ← expr_with_type_to_string h,
                           return ("backtracking assumption " ++ s)))

meta def try_contradictions (cont : tactic unit) :=
do ctx ← local_context,
   goal ← target,
   first $ list.for ctx (λ h, do
     ht ← infer_type h,
     unneg_ht ← match_not ht,
     first $ list.for ctx (λ h', do
       ht' ← infer_type h',
       unify ht' unneg_ht,
       t ← mk_app ``absurd [goal, h', h],
       auto_trace_stepM (exact t)
         (λ u, do s₁ ← expr_with_type_to_string h',
                  s₂ ← expr_with_type_to_string h,
                  return ("try using contradiction " ++ s₁ ++ ", " ++ s₂)),
       auto_trace_with_fail_messageM cont
         (λ u, do s₁ ← expr_with_type_to_string h',
                  s₂ ← expr_with_type_to_string h,
                  return ("backtracking contradiction " ++ s₁ ++ ", " ++ s₂))))


/- instantiating quantifiers in the backtracking search -/

meta def has_forall_type (h : expr) : tactic bool :=
do ht ← infer_type h,
   is_forall ht

-- TODO: eliminate
meta def apply_to_metavars_while_universal_aux : unit → expr → tactic expr
| unit.star h :=
do ht ← infer_type h,
   if head_symbol ht ≠ `pi then return h
   else do
     htt ← infer_type ht,
     if htt ≠ prop then return h
     else do
       dt ← infer_type (binding_domain ht),
       if dt = prop then return h
       else do
         v ← mk_meta_var (binding_domain ht),
         apply_to_metavars_while_universal_aux unit.star (expr.app h v)

meta def apply_to_metavars_while_universal (h : expr) : tactic expr :=
apply_to_metavars_while_universal_aux unit.star h

meta def try_instantiate_quantifiers (cont : tactic unit) : tactic unit :=
do hs ← (local_context >>= monad.filterM has_forall_type),
   gt ← target,
   when (hs = []/- ∧ head_symbol gt ≠ `Exists-/) failed,
   monad.forM' hs
     (λ h, do h' ← apply_to_metavars_while_universal h,
           assert_fresh h'),
--   when (head_symbol gt = `Exists) split,
   monad.forM' hs clear,
   monad.whenb (is_trace_enabled_for `auto)
     (trace "instantiating quantifiers" >> trace_state >> trace "-----"),
   cont

/-
  Safe automation. These operate on the first goal, and apply only safe rules (the new
  state is logically equivalent to the original one). They make whatever progress they
  can, and leave the user with zero or more goals.

  They take the following arguments:

  classical     : classical or intuitionistic
  use_simp      : whether to use the simplifier
  simp_lemmas   : in the latter case, extra lemmas to use
-/

-- perform safe rules that do not split the goal
meta def clarify_core (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database) (nedb : nelim_rule_database)
    (simp_lemmas : list expr) :
  tactic unit :=
do repeat (apply_intro_rule idb 1 classical),
   repeat (apply_elim_rule edb nedb 1 classical),
   repeat try_subst_and_injection_on_hyps,
   (now <|> assumption_safe <|> -- contradiction_safe <|>
     when (use_simp = tt)
       (do when_tracing `auto (trace "calling simplifier"),
          try (strong_simp_hyps_add simp_lemmas),
          try (strong_simp_add simp_lemmas),
          try (now <|> assumption_safe)))

-- perform safe rules
-- TODO: fix recursion
meta def safe_core (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database) (nedb : nelim_rule_database)
    (simp_lemmas : list expr) :
  unit → tactic unit
| unit.star :=
do clarify_core classical use_simp idb edb nedb simp_lemmas,
   now <|>
     try ((apply_intro_rule idb 10 classical <|> apply_elim_rule edb nedb 10 classical) ;
        (safe_core /- classical use_simp idb edb nedb simp_lemmas -/ unit.star))

/-
  The backtracking tableau prover.

  The function force_all_core_aux is the heart of the tableau prover. It takes a list of goals,
  which are assumed to have been processed with the safe rules already and are not visible on the
  goal stack. It applies safe rules to the goals in the current goal list (if any),
  and then starts calling backtracking rules.

  This function is meant to be passed as a continuation to the backtracking tactics, which are
  called with a single goal. The tactics should operate on the goal, resulting in a new goal
  list. They should then call the continuation to finish the backtracking search.

  The function succeeds if all the goals are ultimately proved, and it fails otherwise.
-/

-- TODO: fix recursion
meta def force_all_core_aux (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database) (nedb : elim_rule_database)
    (bidb : bintro_rule_database) (bedb : belim_rule_database) (bnedb : belim_rule_database)
    (simp_lemmas : list expr)
    (final_check : tactic unit) /- (preprocessed_goals : list expr) -/ :
  unit → list expr → tactic unit
| unit.star :=
let force_core_rec := force_all_core_aux /- classical use_simp idb edb nedb bidb bedb bnedb
                                         simp_lemmas final_check -/ unit.star in
let process_goals_with_backtracking : list expr → tactic unit :=
  λ l, match l with
       | []        := final_check   -- if it passes, we have success!
       | (g :: gs) :=
         do {set_goals [g],
             try_assumptions (force_core_rec gs) <|>
             try_contradictions (force_core_rec gs) <|>
             try_instantiate_quantifiers (force_core_rec gs) <|>
             apply_bintro_rule bidb 10 classical (force_core_rec gs) <|>
             apply_belim_rule bedb bnedb 10 classical (force_core_rec gs)}
       end in
λ preprocessed_goals,
do n ← num_goals,
   if n ≠ 0 then do
     all_goals (safe_core classical use_simp idb edb nedb simp_lemmas unit.star),
     gs ← get_goals,
     set_goals [],
     force_all_core_aux /-classical use_simp idb edb nedb bidb bedb bnedb simp_lemmas final_check-/
                        unit.star (gs ++ preprocessed_goals)
   else do
     process_goals_with_backtracking preprocessed_goals

meta def final_check_for_metavariables (g : expr) : tactic unit :=
do result ← instantiate_mvars g,
   monad.whenb (has_meta_var result)
   (when_tracing `auto (trace_state >> trace "result has metavariables:" >> trace result) >>
     failed)

-- the main tableaux prover: acts on one goal, makes sure there are no metavariables at the end
meta def force_core (classical : bool) (use_simp : bool)
    (idb : intro_rule_database) (edb : elim_rule_database) (nedb : elim_rule_database)
    (bidb : bintro_rule_database) (bedb : belim_rule_database) (bnedb : belim_rule_database)
    (simp_lemmas : list expr) :
  tactic unit :=
do auto_trace_step skip (λ u, ">>> entering force"),
   gs ← get_goals,
   match gs with
   | [] := fail "force failed, there are no goals"
   | (g :: gs') := do set_goals [g],
                      force_all_core_aux classical use_simp idb edb nedb bidb bedb bnedb simp_lemmas
                        (final_check_for_metavariables g) unit.star [],
                      set_goals gs
   end


/- front ends -/

-- applies to first goal, never splits it, applies only safe rules, always succeeds
meta def clarify (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (nerules : list elim_rule)
    (simp_lemmas : list expr) :
  tactic unit :=
let idb := initialize_rule_database (standard_intro_rules ++ irules),
    edb := initialize_rule_database (standard_elim_rules ++ erules),
    nedb := initialize_rule_database (standard_nelim_rules ++ nerules) in
clarify_core classical use_simp idb edb nedb simp_lemmas

-- applies to first goal, applies only safe rules, always succeeds
meta def safe (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (nerules : list elim_rule)
    (simp_lemmas : list expr) :
  tactic unit :=
let idb := initialize_rule_database (standard_intro_rules ++ irules),
    edb := initialize_rule_database (standard_elim_rules ++ erules),
    nedb := initialize_rule_database (standard_nelim_rules ++ nerules) in
safe_core classical use_simp idb edb nedb simp_lemmas unit.star

-- applies safe to all goals
meta def safe_all (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (nerules : list elim_rule)
    (simp_lemmas : list expr) :
  tactic unit :=
all_goals (safe classical use_simp irules erules nerules simp_lemmas)

-- applies to first goal, fails if it does not solve it
meta def force (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (nerules : list elim_rule)
    (birules : list bintro_rule) (berules : list belim_rule) (bnerules : list belim_rule)
    (simp_lemmas : list expr) :
  tactic unit :=
let idb := initialize_rule_database (standard_intro_rules ++ irules),
    bidb := initialize_rule_database (standard_bintro_rules ++ birules),
    edb := initialize_rule_database (standard_elim_rules ++ erules),
    nedb := initialize_rule_database (standard_nelim_rules ++ nerules),
    bedb := initialize_rule_database (standard_belim_rules ++ berules),
    bnedb := initialize_rule_database (standard_bnelim_rules ++ bnerules) in
force_core classical use_simp idb edb nedb bidb bedb bnedb simp_lemmas

-- applies to all goals, always succeeds
meta def auto (classical : bool) (use_simp : bool)
    (irules : list intro_rule) (erules : list elim_rule) (nerules : list elim_rule)
    (birules : list bintro_rule) (berules : list belim_rule) (bnerules : list belim_rule)
    (simp_lemmas : list expr) :
  tactic unit :=
safe_all classical use_simp irules erules nerules simp_lemmas >>
all_goals
  (try (force classical use_simp irules erules nerules birules berules bnerules simp_lemmas))


/- for testing -/

meta def clarify' : tactic unit := clarify tt ff [] [] [] []

meta def safe' : tactic unit := safe tt ff [] [] [] []

meta def ssafe' : tactic unit := safe tt tt [] [] [] [] -- with simplification

meta def force' : tactic unit := force tt ff [] [] [] [] [] [] []

meta def sforce' : tactic unit := force tt tt [] [] [] [] [] [] []

meta def auto' : tactic unit := auto tt ff [] [] [] [] [] [] []

meta def sauto' : tactic unit := auto tt tt [] [] [] [] [] [] []

meta def iauto' : tactic unit := auto ff ff [] [] [] [] [] [] []

meta def isauto' : tactic unit := auto ff tt [] [] [] [] [] [] []

end tactic
