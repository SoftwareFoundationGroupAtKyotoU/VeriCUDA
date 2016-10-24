open Print
open Verifier
open Why3util

(** ---------------- interactive mode *)
exception InvalidCommand

type config = {
  c_tasks : Why3.Task.task list;
  c_admitted : Why3.Task.task list;
  c_undo_stack : config list;
}

let make_initial_config tasks =
  { c_tasks = tasks; c_admitted = []; c_undo_stack = [] }

let rec read_command () =
  try 
    match read_line () |> Str.split (Str.regexp "[ \t\n\r]+") with
    | [] -> read_command ()
    | cmd :: args -> cmd, args
  with End_of_file ->
    Format.printf "exited.@."; exit 0

let apply_on_current_task_l f config =
  match config.c_tasks with
  | [] -> config
  | task::tasks -> 
     { config with c_tasks = f task @ tasks;
                   c_undo_stack = config :: config.c_undo_stack }

let apply_on_current_task f config =
  match config.c_tasks with
  | [] -> config
  | task::tasks -> 
     { config with c_tasks = f task :: tasks;
                   c_undo_stack = config :: config.c_undo_stack }

let show_command n config =
  assert (0 < n && n <= List.length config.c_tasks);
  if n = 1 then
    Format.printf "Current task:@."
  else
    Format.printf "Task #%d:@." n;
  print_task_short (List.nth config.c_tasks (n - 1)) None

let command_descriptions =
  ["show", "show [n | all]: show goals";
   "split", "split: split current goal";
   "compute", "compute: compute redexes in current goal";
   "why3trans", "why3trans trans [n]: apply why3 transformation";
   "rewrite", "rewrite: rewrite using equalities in hypotheses";
   "decompose_quant", "decompose_quant: decompose quantification on threads\
                       and dim3";
   "merge_quant", "merge_quant: merge quantifications";
   "simp_quant", "simp_quant: decompose and merge quantifiers";
   "qe", "qe: eliminate quantifiers";
   "prove", "prove [all]: try to discharge current/all goal(s) using \
             SMT solvers";
   "quit", "quit: quit";
   "undo", "undo: undo";
   "admit", "admit: amdit current goal";
   "postpone", "postpone: postpone current goal";
   "congruence", "congruence: try congruence";
   "auto_simp", "auto_simp: automatically simplify current task";
   "help", "help [cmd]: show help message";
  ]

let do_command cmd args config =
  match cmd, args with
  | "show", [] ->
     if config.c_tasks = [] then
       Format.printf "No further tasks.@."
     else show_command 1 config;
     config
  | "show", ["all"] ->
     for i = 1 to List.length config.c_tasks do
       show_command i config;
       print_newline ()
     done;
     config
  | "show", [arg] ->
     begin
       match try Some (int_of_string arg) with Failure _ -> None with
       | Some n ->
         if 0 < n && n <= List.length config.c_tasks then
           show_command n config
         else
           Format.printf "no such task: %d@." n
       | None ->
          Format.printf "no such task: %s@." arg
     end;
     config
  | "split", [] ->
     apply_on_current_task_l (apply_why3trans "split_goal_full") config
  | "compute", [] ->
     apply_on_current_task_l (apply_why3trans "compute_specified") config
  | "why3trans", [trans] ->
     apply_on_current_task_l (apply_why3trans trans) config
  | "why3trans", [trans; n] ->
     { config with
       c_tasks =
         List.concat @@ 
           List.mapi (fun i task -> if string_of_int i = n then
                                      apply_why3trans trans task
                                    else [task])
                     config.c_tasks;
       c_undo_stack = config :: config.c_undo_stack }
  | "rewrite", [] ->
     apply_on_current_task_l Vctrans.rewrite_using_premises config
  | "decompose_quant", [] ->
     apply_on_current_task
       (task_map_decl Vctrans.decompose_thread_quant)
       config
  | "merge_quant", [] ->
     apply_on_current_task
       (task_map_decl Vctrans.merge_quantifiers)
       config
  | "simp_quant", [] ->
     config
     |> apply_on_current_task
          (task_map_decl Vctrans.decompose_thread_quant)
     |> apply_on_current_task
          (task_map_decl Vctrans.merge_quantifiers)
  | "qe", [] ->
     apply_on_current_task Vctrans.eliminate_linear_quantifier config
  | "prove", [] ->
     apply_on_current_task_l
       (fun task -> if try_prove_task task then [] else [task])
       config
  | "prove", ["all"] ->
     { config with
       c_tasks = List.fold_left (fun acc task ->
                                 if try_prove_task task then acc else task :: acc)
                                [] config.c_tasks;
       c_undo_stack = config :: config.c_undo_stack }
  | "quit", [] -> exit 0
  | "undo", [] ->
     begin
       match config.c_undo_stack with
       | [] -> Format.printf "No further undos.@."; config
       | config' :: _ -> config'
     end
  | "admit", [] ->
     begin
       match config.c_tasks with
       | [] -> Format.printf "Nothing to admit.@."; config
       | task :: tasks ->
          Format.printf "Admitted the current task.@.";
          { c_tasks = tasks;
            c_admitted = task :: config.c_admitted;
            c_undo_stack = config :: config.c_undo_stack }
     end
  | "postpone", [] ->
     begin
       match config.c_tasks with
       | []
       | [_] -> Format.printf "Nothing to postpone.@."; config
       | task :: tasks ->
          { config with c_tasks = tasks @ [task];
                        c_undo_stack = config :: config.c_undo_stack }
     end
  | "congruence", [] ->
     let apply_congruence goal =
       match Vctrans.apply_congruence goal with
       | None -> goal
       | Some goal' -> goal'
     in
     apply_on_current_task (transform_goal apply_congruence) config
  | "auto_simp", [] ->
     let apply_congruence goal =
       match Vctrans.apply_congruence goal with
       | None -> goal
       | Some goal' -> goal'
     in
     apply_on_current_task (transform_goal apply_congruence) config
  | "help", [] ->
     List.iter (fun (_, desc) -> Format.printf "%s@." desc)
               command_descriptions;
     config
  | "help", [cmd] ->
     begin
       try
         let desc = List.assoc cmd command_descriptions in
         Format.printf "%s@." desc
       with
         Not_found -> Format.printf "Unknown command: %s@." cmd
     end;
     config
  | _, _ ->
     raise InvalidCommand

let rec repl config =
  Format.printf "%d task%s> @?"
                (List.length config.c_tasks)
                (if List.length config.c_tasks = 1 then "" else "s");
  let cmd, args = read_command () in
  begin
    try
      do_command cmd args config
    with
      InvalidCommand ->
      Format.printf "invalid command@.";
      config
  end
  |> repl

let rec start_repl tasks = repl @@ make_initial_config tasks
