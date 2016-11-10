type task_tree
val repeat_on_term :
  (Why3.Term.term -> Why3.Term.term) -> Why3.Term.term -> Why3.Term.term
(* val simplify_formula : Why3.Term.term -> Why3.Term.term *)
val simplify_task : Why3.Task.task -> task_tree
val prover_name_list : string list
val try_prove_task :
  ?provers:string list ->
  ?timelimit:int -> ?memlimit:int -> Why3.Task.task -> bool
val generate_task : string -> string -> Why3.Task.task list
(* val t_size : Why3.Term.term -> int
 * val decl_size : Why3.Theory.tdecl -> int
 * val task_size : Why3.Task.task -> int
 * val print_task_size : Why3.Task.task list -> unit *)
val verify_spec : string -> string -> unit
