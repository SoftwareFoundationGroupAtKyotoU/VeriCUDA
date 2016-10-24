
let print_task task outname full =
  let ch = match outname with
    | None -> stdout
    | Some name ->
       let dir = Filename.dirname name in
       ignore @@ Sys.command @@ "mkdir -p " ^ dir;
       open_out name
  in
  let f = Format.formatter_of_out_channel ch in
  if full then
    Format.fprintf f "%a@." Why3.Pretty.print_task task
  else
    begin 
      (* Format.fprintf f "Task:@."; *)
      let decls = Why3.Task.task_decls task in
      List.iter
        (fun decl ->
         match decl.Why3.Decl.d_node with
         | Why3.Decl.Dprop (k, pr, t)
              when k = Why3.Decl.Pgoal
                   || let name = pr.Why3.Decl.pr_name.Why3.Ident.id_string in
                      Str.string_match (Str.regexp "^vc_premise_") name 0
           -> Format.fprintf f "  @[%a@]@." Why3.Pretty.print_decl decl
         | _ -> ())
        decls;
      Format.fprintf f "end@.";
      match outname with
      | None -> ()
      | Some name -> Printf.eprintf "vc is written in %s.\n" name
    end
    

let print_task_full task outname = print_task task outname true

let print_task_short task outname = print_task task outname false

let print_result prover result =
  Format.printf "%s returns %a in %f seconds@."
                prover
                Why3.Call_provers.print_prover_answer
                result.Why3.Call_provers.pr_answer
                result.Why3.Call_provers.pr_time
                (* result.Why3.Call_provers.pr_output *)

let rec print_exception = function
  | Why3.Ty.TypeMismatch (ty1, ty2) ->
     Format.printf "error: Type mismatch:@[ %a vs. %a@]@."
                   Why3.Pretty.print_ty ty1 Why3.Pretty.print_ty ty2
  | Why3.Decl.UnknownIdent(id) ->
     Printf.printf "Unknown identifier: %s\n" id.Why3.Ident.id_string
  | Why3.Decl.UnboundVar(vs) ->
     Format.printf "Unbound variable: %a\n" Why3.Pretty.print_vs vs
  | Why3.Env.LibraryNotFound(p) ->
     Format.printf "Library not found: [%s]@." @@
       String.concat "; " p
  | Why3.Loc.Located (loc, e') as e ->
     Why3.Exn_printer.exn_printer (Format.formatter_of_out_channel stdout)
                                  e;
     print_exception e'
  | e -> Why3.Exn_printer.exn_printer (Format.formatter_of_out_channel stdout)
                                      e
