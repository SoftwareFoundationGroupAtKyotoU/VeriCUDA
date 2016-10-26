open Why3api
open Why3util
open Vc
open Vcg
open Utils
open Print
open ExtList

let print_exn_flag = ref false
let print_task_style = ref "full"
let prove_flag = ref true
let trans_flag = ref true
let default_timelimit = ref 1
let default_memlimit = ref 4000
let interactive_flag = ref false
let inline_assignment = ref true
let print_size_flag = ref false
let parse_only_flag = ref false

let decl_size { Why3.Theory.td_node = n } =
  match n with
  | Why3.Theory.Decl { Why3.Decl.d_node = d } ->
     begin
       (* count only lemma, axiom, goal, and skip *)
       match d with
       | Why3.Decl.Dprop (_, _, t) -> t_size t
       | _ -> 0
     end
  | _ -> 0

let task_size task =
  Why3.Task.task_fold (fun n td -> n + decl_size td) 0 task

(* ---------------- cuda program file -> Cil *)

let parse_file filename =
  let f = Frontc.parse filename () in
  Rmtmps.removeUnusedTemps f;
  f

let find_decl file name =
  let rec find = function
    | Cil.GFun (dec, _) :: rest when dec.Cil.svar.Cil.vname = name ->
       dec
    | _ :: rest -> find rest
    | [] -> raise Not_found
  in find file.Cil.globals


(* ---------------- transform task *)
let rec repeat_on_term f t =
  let t' = f t in
  if Why3.Term.t_equal t t' then t else repeat_on_term f t'

let rec simplify_formula t =
  let f t =
    t
    |> Vctrans.decompose_thread_quant
    |> Vctrans.merge_quantifiers
  in
  repeat_on_term f t

let simplify_task task =
  task
  |> Vctrans.rewrite_using_premises
  |> List.map @@ (task_map_decl simplify_formula)
  |> List.map @@ Vctrans.rewrite_using_simple_premises
  |> List.concat
  |> List.map @@ apply_why3trans "split_goal_right"
  |> List.concat
  |> List.map @@ (task_map_decl simplify_formula)
  |> List.map @@ Vctrans.eliminate_linear_quantifier
  |> List.map @@ (task_map_decl simplify_formula)
  |> List.map @@ Vctrans.simplify_affine_formula
  |> List.map (apply_why3trans "compute_specified")
  |> List.concat

let prover_name_list = ["alt-ergo"; "cvc3"; "cvc4"; "z3"; "eprover"]

let kill_prover_calls pcs =
  List.iter
    (fun (_, p) ->
     match Why3.Call_provers.query_call p with
     | None ->
        Unix.kill (Why3.Call_provers.prover_call_pid p) Sys.sigterm;
        (* this cleanups temporary files; better way to do this? *)
        ignore @@ Why3.Call_provers.wait_on_call p ()
     | Some postpc -> ignore @@ postpc ())
    pcs

exception Finished

let try_prove_task ?(provers=prover_name_list)
                   ?(timelimit=(!default_timelimit))
                   ?(memlimit=(!default_memlimit)) task =
  let pcs = List.map
              (fun name ->
               let pcall = prove_task ~timelimit ~memlimit name task () in
               name, pcall)
              provers
  in
  let filter_finished pcs =
    let rec f pcs finished running = match pcs with
      | [] -> finished, running
      | pc :: pcs' ->
         match Why3.Call_provers.query_call @@ snd pc  with
         | None -> f pcs' finished (pc :: running)
         | Some r -> f pcs' ((fst pc, r ()) :: finished) running
    in f pcs [] []
  in
  let rec check pcs =
    let finished, running = filter_finished pcs in
    List.iter (fun (name, result) ->
               print_result name result;
               (* for debugging; print task if inconsistent assumption
                   is reported *)
               if Str.string_match (Str.regexp "Inconsistent assumption")
                                   result.Why3.Call_provers.pr_output 0
               then
                 (Format.printf "Task with inconsistent assumption:@.";
                  print_task_short task None);
               if result.Why3.Call_provers.pr_answer = Why3.Call_provers.Valid
               then
                 begin
                   (* The task has already been proved.
                    * We don't need to run other provers on this task any more,
                    * so try to kill the processes. *)
                   kill_prover_calls running;
                   raise Finished
                 end)
              finished;
    if running = [] then false
    else
      (* wait for a while and try again  *)
      (* (Unix.select [] [] [] 0.1; check running) *)
      (* (Unix.sleep 1; check running) *)
      (* (ignore @@ Unix.system "sleep 0.1"; check running) *)
      (Unix.sleepf 0.1; check running)
  in
  Format.printf "Calling provers...@.";
  try check pcs with Finished -> true

let generate_task filename funcname =
  let file = parse_file filename in
  debug "parsed file %s" filename;
  let fdecl = find_decl file funcname in
  if !parse_only_flag then
    begin
      Cil.printCilAsIs := true;
      let sep = String.make 70 '=' in
      ignore @@ Pretty.printf "%s@!Parser output:@!%a@!%s@!"
                              sep Cil.d_block fdecl.Cil.sbody sep;
      exit 0
    end;
  let vcs = generate_vc file fdecl in
  let tasks = List.map (fun vc ->
                        Taskgen.task_of_vc !inline_assignment vc)
                       vcs in
  if !trans_flag then
    (debug "%d tasks before transformation@." (List.length tasks);
     List.concat @@ List.map simplify_task tasks)
  else tasks

let print_task_size tasks =
  let sizes = List.map task_size tasks in
  List.iteri (fun i n ->
              Format.printf "Task #%d has size %d@."
                            (i + 1) n)
             sizes;
  Format.printf "Total size %d@." @@
    List.fold_left (+) 0 sizes

let verify_spec filename funcname =
  let tasks = generate_task filename funcname in
  Format.printf "generated %d tasks.@." (List.length tasks);
  if !print_size_flag then print_task_size tasks;
  if !prove_flag then
    let tasks' = List.filter (fun t -> not (try_prove_task ~timelimit:1 t)) tasks in
    debug "eliminating mk_dim3...@.";
    let tasks' = List.filter (fun t ->
                              Vctrans.eliminate_ls Why3api.fs_mk_dim3 t
                              |> task_map_decl simplify_formula
                              |> Vctrans.eliminate_linear_quantifier
                              |> task_map_decl simplify_formula
                              |> apply_why3trans "compute_specified"
                              (* |> List.map (fun t -> print_task_short t None; t) *)
                              |> List.for_all (try_prove_task ~timelimit:1)
                              |> not)
                             (List.rev tasks')
    in
    (* ----try congruence *)
    (* debug_flag := true; *)
    let trans_congruence task =
      let _, task' = Why3.Task.task_separate_goal task in
      (* debug "trying congruence on:@.  %a@." Why3.Pretty.print_task task; *)
      match Vctrans.apply_congruence @@ Why3.Task.task_goal_fmla task with
      | None -> None
      | Some goal ->
         Some (Why3.Task.add_decl task' @@
                 Why3.Decl.create_prop_decl Why3.Decl.Pgoal
                                            (Why3.Task.task_goal task)
                                            goal
               |> apply_why3trans "split_goal_right"
               |> List.map @@ apply_why3trans "compute_specified"
               |> List.concat
               |> List.map @@ task_map_decl simplify_formula
               |> List.map @@ Vctrans.eliminate_linear_quantifier
               |> List.map @@ task_map_decl simplify_formula)
    in
    let rec f n task =
      if n = 0 then
        false
      else
        match trans_congruence task with
        | None -> false
        | Some tasks ->
           List.filter (fun t -> not (try_prove_task t)) tasks
           |> List.for_all @@ f (n - 1)
    in
    debug "trying congruence...@.";
    let tasks' = List.filter (fun t -> not @@ f 10 t) tasks' in
    (* ----try eliminate-equality *)
    debug "trying eliminate equality...@.";
    let try_elim_eq task =
      let task' = transform_goal Vctrans.replace_equality_with_false task in
      let tasks =
        if !trans_flag then
          task'
          |> task_map_decl simplify_formula
          |> Vctrans.eliminate_linear_quantifier
          |> task_map_decl simplify_formula
          |> apply_why3trans "compute_specified"
        else [task']
      in
      not @@ (List.for_all try_prove_task tasks)
    in
    let tasks' = List.filter try_elim_eq (List.rev tasks') in
    (* print unsolved tasks *)
    List.iter (fun task ->
               if !print_task_style = "full" then
                 begin
                   Format.printf "Unsolved task: #%d:@." (Why3.Task.task_hash task);
                   print_task_full task None
                 end
               else if !print_task_style = "short" then
                 begin
                   Format.printf "Unsolved task: #%d:@." (Why3.Task.task_hash task);
                   print_task_short task None
                 end)
              tasks';
    (* List.iter Vctrans.collect_eqns_test tasks'; *)
    if tasks' <> [] then
      Format.printf "%d unsolved task%s.@."
                    (List.length tasks') (* (List.length tasks) *)
                    (if List.length tasks' = 1 then "" else "s")
    else
      Format.printf "Verified!@."
  else
    if !print_task_style = "full" then
      List.iter (fun task ->
                 Format.printf "Task #%d:@." (Why3.Task.task_hash task);
                 print_task_full task None)
                tasks
    else if !print_task_style = "short" then
      List.iter (fun task ->
                 Format.printf "Task #%d:@." (Why3.Task.task_hash task);
                 print_task_short task None)
                tasks
