val decompose_thread_quant : Why3.Term.term -> Why3.Term.term

val eliminate_unique_quant : Why3.Term.term -> Why3.Term.term

(* val reduce_quant : Why3.Term.term -> Why3.Term.term *)

val merge_quantifiers : Why3.Term.term -> Why3.Term.term

val eliminate_existential_in_premises : Why3.Task.task -> Why3.Task.task

val collect_eqns_test : Why3.Task.task -> unit
val rewrite_using_premises : Why3.Task.task -> Why3.Task.task list
val rewrite_using_simple_premises :
  Why3.Task.task -> Why3.Task.task list

val eliminate_linear_quantifier_t : Why3.Term.term -> Why3.Term.term

val eliminate_linear_quantifier : Why3.Task.task -> Why3.Task.task

val bind_epsilon_by_let : Why3.Term.term -> Why3.Term.term

val apply_congruence : Why3.Term.term -> Why3.Term.term option

val replace_equality_with_false : Why3.Term.term -> Why3.Term.term

val eliminate_ls : Why3.Term.lsymbol -> Why3.Task.task -> Why3.Task.task

val simplify_affine_formula : Why3.Task.task -> Why3.Task.task
