open tactic

/- mk_inthabitant_using A t assumes A is an expression denoting a type. It creates
   a goal with type A, applies t, and returns the expression that results. -/
meta_definition mk_inhabitant_using (A : expr) (t : tactic unit) : tactic expr :=
do m ← mk_meta_var A,
   gs ← get_goals,
   set_goals [m],
   t,
   r ← instantiate_mvars m,
   set_goals gs,
   return r

meta_definition my_tac : tactic expr :=
do A ← to_expr `(true ∧ true),
   mk_inhabitant_using A (trace_state >> repeat constructor)

run_command my_tac >>= trace
