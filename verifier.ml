open Why3api
open Why3util
open Vc
open Vcg
open Utils
open Print
open ExtList

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
type task_tree =
  | TTLeaf of Why3.Task.task
  | TTLazy of task_tree lazy_t (* currently this is not used *)
  | TTAnd of task_tree list
  | TTOr of task_tree list
  | TTSuccess                   (* no more task to solve *)
  | TTFail                      (* unsolvable task; currently there is
                                 * no possibilty of arising this during
                                 * verification process, because we use
                                 * no refutation procedure. *)

let tt_and = function
  | [] -> TTSuccess
  | [tt] -> tt
  | tts -> TTAnd tts

let tt_or = function
  | [] -> TTFail                (* probably should not happen *)
  | [tt] -> tt
  | tts -> TTOr tts

let rec task_tree_equal tt1 tt2 =
  match tt1, tt2 with
  | TTLeaf t1, TTLeaf t2 -> Why3.Task.task_equal t1 t2
  | TTLazy x, TTLazy y -> x == y
  | TTAnd tts1, TTAnd tts2
  | TTOr tts1, TTOr tts2 ->
     List.length tts1 = List.length tts2 &&
       List.for_all2 task_tree_equal tts1 tts2
  | TTSuccess, TTSuccess
  | TTFail, TTFail -> true
  | _, _ -> false

let rec reduce_task_tree = function
  | TTLeaf _ as tt -> tt
  | TTLazy _ as tt -> tt
  | TTAnd tts ->
     let tts' = List.map reduce_task_tree tts in
     if List.mem TTFail tts' then TTFail
     else List.remove_all tts' TTSuccess
          |> List.unique ~cmp:task_tree_equal
          |> tt_and
  | TTOr tts ->
     let tts' = List.map reduce_task_tree tts in
     if List.mem TTSuccess tts' then TTSuccess
     else List.remove_all tts' TTFail
          |> List.unique ~cmp:task_tree_equal
          |> tt_or
  | TTSuccess -> TTSuccess
  | TTFail -> TTFail

let print_task_size tasks =
  let sizes = List.map task_size tasks in
  List.iteri (fun i n ->
              Format.printf "Task #%d has size %d@."
                            (i + 1) n)
             sizes;
  Format.printf "Total size %d@." @@
    List.fold_left (+) 0 sizes

let rec task_tree_size = function
  | TTLeaf t -> task_size t
  | TTLazy t -> task_tree_size (Lazy.force t)
  | TTAnd tts
  | TTOr tts -> List.fold_left (+) 0 (List.map task_tree_size tts)
  | TTSuccess
  | TTFail -> 0

(* let rec tree_map fn tree =
 *   match tree with
 *   | TTLeaf t -> fn t
 *   | TTAnd tts -> TTAnd (List.map (tree_map fn) tts)
 *   | TTOr tts -> TTOr (List.map (tree_map fn) tts)
 *   | TTSuccess
 *   | TTFail -> tree *)

let rec try_on_task_tree prove = function
  | TTLeaf task as tree -> if prove task then TTSuccess else tree
  | TTLazy x -> try_on_task_tree prove @@ Lazy.force x
  | TTAnd tts ->
     List.map (try_on_task_tree prove) tts
     |> List.filter ((<>) TTSuccess)
     |> tt_and
  | TTOr tts ->
     (* Refrain from using List functions to avoid eagerly trying to
      * prove all the tasks in [tts]: solving one of them suffices. *)
     let rec try_any tts acc =
       (* Returns empty list if some of the subtree is proved. *)
       match tts with
       | [] -> tt_or (List.rev acc)
       | tt :: tts' ->
          let tt' = try_on_task_tree prove tt in
          (* Success if one of them is solved *)
          if tt' = TTSuccess then TTSuccess
          else try_any tts' (tt' :: acc)
     in
     try_any tts []
  | TTSuccess -> TTSuccess
  | TTFail -> TTFail

let print_task task =
  if !Options.print_task_style = "full" then
    begin
      Format.printf "Unsolved task: #%d:@." (Why3.Task.task_hash task);
      print_task_full task None
    end
  else if !Options.print_task_style = "short" then
    begin
      Format.printf "Unsolved task: #%d:@." (Why3.Task.task_hash task);
      print_task_short task None
    end

let print_task_list tasks = List.iter print_task tasks

let rec print_all_tasks = function
  | TTLeaf task -> print_task task
  | TTLazy x -> print_all_tasks (Lazy.force x) (* should this be forced? *)
  | TTAnd tts
  | TTOr tts -> List.iter print_all_tasks tts
  | TTSuccess
  | TTFail -> ()

let rec print_task_tree tt =
  let rec pp_structure fmt tt =
    match tt with
    | TTSuccess -> Format.pp_print_string fmt "<proved>"
    | TTFail -> assert false
    | TTLeaf task -> Format.pp_print_int fmt (Why3.Task.task_hash task)
    | TTLazy _ -> Format.pp_print_string fmt "<lazy>"
    | TTAnd tts ->
       Format.printf "(And %a)"
                     (Format.pp_print_list
                        ~pp_sep:(fun f _ -> Format.pp_print_string f " ")
                        pp_structure)
                     tts
    | TTOr tts ->
       Format.printf "(Or %a)"
                     (Format.pp_print_list
                        ~pp_sep:(fun f _ -> Format.pp_print_string f " ")
                        pp_structure)
                     tts
  in
  Format.printf "%a@." pp_structure tt

let rec task_tree_count = function
  | TTSuccess
  | TTFail -> 0
  | TTLeaf _ -> 1
  | TTLazy _ -> 1
  | TTAnd tts -> List.fold_left (+) 0 (List.map task_tree_count tts)
  | TTOr tts -> 1

let rec repeat_on_term f t =
  let t' = f t in
  if Why3.Term.t_equal t t' then t else repeat_on_term f t'

let simplify_task task =
  let tasks =
    (* common simplification *)
    task
    |> Vctrans.rewrite_using_premises
    (* |> List.map @@ (task_map_decl simplify_formula) *)
    |> List.map @@
         (task_map_decl (repeat_on_term Vctrans.decompose_thread_quant))
    |> List.map @@ Vctrans.rewrite_using_simple_premises
    |> List.concat
    |> List.map @@ apply_why3trans "split_goal_right"
    |> List.concat
    |> List.map @@ (task_map_decl simplify_formula)
  in
  let simplify task =
    let tasks1 =
      (* merge -> qe *)
      task
      |> task_map_decl (repeat_on_term Vctrans.merge_quantifiers)
      |> Vctrans.eliminate_linear_quantifier
      |> task_map_decl simplify_formula
      |> Vctrans.simplify_affine_formula
      |> apply_why3trans "compute_specified"
      |> List.unique ~cmp:Why3.Task.task_equal
      |> List.map (fun x -> TTLeaf x)
    in
    let tasks2 =
      (* no merging, only affine expression simplification *)
      task
      |> Vctrans.simplify_affine_formula
      |> Vctrans.eliminate_linear_quantifier
      |> task_map_decl simplify_formula
      |> apply_why3trans "compute_specified"
      |> List.unique ~cmp:Why3.Task.task_equal
      |> List.map (fun x -> TTLeaf x)
    in
    tt_or [tt_and tasks1; tt_and tasks2]
  (* the following wasn't as effective as expected... *)
  (* tt_or [TTLazy (lazy (tt_and tasks1)); TTLazy (lazy (tt_and tasks2))] *)
  in
  tt_and (List.map simplify tasks) |> reduce_task_tree

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
                   ?(timelimit=(!Options.timelimit))
                   ?(memlimit=(!Options.memlimit)) task =
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
               (* print_result name result; *)
               (* for debugging; print task if inconsistent assumption
                   is reported *)
               (* if Str.string_match (Str.regexp "Inconsistent assumption")
                *                     result.Why3.Call_provers.pr_output 0
                * then
                *   (Format.printf "Task with inconsistent assumption:@.";
                *    print_task_short task None); *)
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
  (* Format.printf "Calling provers...@."; *)
  try check pcs with Finished -> true

let generate_task filename funcname =
  let file = parse_file filename in
  debug "parsed file %s" filename;
  let fdecl = find_decl file funcname in
  if !Options.parse_only_flag then
    begin
      Cil.printCilAsIs := true;
      let sep = String.make 70 '=' in
      ignore @@ Pretty.printf "%s@!Parser output:@!%a@!%s@!"
                              sep Cil.d_block fdecl.Cil.sbody sep;
      exit 0
    end;
  let vcs = generate_vc file fdecl in
  let tasks = List.map (fun vc ->
                        Taskgen.task_of_vc !Options.inline_assign_flag vc)
                       vcs in
  tasks

let rec count_conjuncts = function
  | TTLeaf _ -> 1
  | TTLazy t -> count_conjuncts (Lazy.force t)
  | TTAnd ts -> List.fold_left (+) 0 (List.map count_conjuncts ts)
  | TTOr ts -> 1
  | TTFail
  | TTSuccess -> 0

let rec count_leaves = function
  | TTLeaf _ -> 1
  | TTLazy t -> count_leaves (Lazy.force t)
  | TTAnd ts
  | TTOr ts -> List.fold_left (+) 0 (List.map count_leaves ts)
  | TTFail
  | TTSuccess -> 0

let verify_spec filename funcname =
  let ttgen () =
    let tasks = generate_task filename funcname in
    let tasks' =
      if !Options.trans_flag then List.map simplify_task tasks
      else List.map (fun t -> TTLeaf t) tasks
    in
    reduce_task_tree @@ tt_and tasks'
  in
  let prove tt () =
    let tt' =
      try_on_task_tree (fun t -> try_prove_task ~timelimit:1 t) tt
      |> reduce_task_tree
    in
    (* print_task_tree tt'; *)
    debug "eliminating mk_dim3...@.";
    let tt' = try_on_task_tree
                (fun t ->
                 Vctrans.eliminate_ls Why3api.fs_mk_dim3 t
                 |> task_map_decl simplify_formula
                 |> Vctrans.eliminate_linear_quantifier
                 |> task_map_decl simplify_formula
                 |> apply_why3trans "compute_specified"
                 (* |> List.map (fun t -> print_task_short t None; t) *)
                 |> List.for_all (try_prove_task ~timelimit:1))
                tt'
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
    let tt'' = try_on_task_tree (fun t -> f 10 t) tt' in
    (* print_task_tree tt''; *)
    (* ----try eliminate-equality *)
    debug "trying eliminate equality...@.";
    let try_elim_eq task =
      let task' = transform_goal Vctrans.replace_equality_with_false task in
      let tasks =
        if !Options.trans_flag then
          task'
          |> task_map_decl simplify_formula
          |> Vctrans.eliminate_linear_quantifier
          |> task_map_decl simplify_formula
          |> apply_why3trans "compute_specified"
        else [task']
      in
      List.for_all try_prove_task tasks
    in
    try_on_task_tree try_elim_eq tt''
  in
  let tt, vcg_time = time ttgen in
  let tt', smt_time = time (prove tt) in
  let n_conj = count_conjuncts tt in
  let n_leaves = count_leaves tt in
  let n_conj' = n_conj - count_conjuncts tt' in
  (* let n_leaves' = n_leaves - count_leaves tt' in *)
  Format.printf "Result: %d %d\n" n_conj' n_conj;
  Format.printf "VCG: %f\n" vcg_time;
  Format.printf "SMT: %f\n" smt_time;
  Format.printf "Size: %d %d\n" (task_tree_size tt) n_leaves
