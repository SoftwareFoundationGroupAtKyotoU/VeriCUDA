(* #use "topfind" *)
(* #require "cil" *)
(* #load "frontc.cmo" *)
open Why3.Term
open Why3api
open Why3util
open Formula
open ExtList
open ExtHashtbl
open Utils
open Vc

(* creating lsymbols of fresh name *)
let ls_set : (string, unit) Hashtbl.t = Hashtbl.create 100

let create_ls name ty =
  let fresh_name =
    if Hashtbl.exists ls_set name
    then
    (* [name] is already used; try new one *)
      let rec search n =
        let new_name = name ^ string_of_int n in
        if Hashtbl.exists ls_set new_name
        then search (n + 1)
        else new_name
      in search 0
    else name
  in
  Hashtbl.add ls_set fresh_name ();
  create_lsymbol (Why3.Ident.id_fresh fresh_name) [] ty


(** cil --> why3 *)

let rec collect_attributes = function
  | Cil.TVoid attrs
  | Cil.TInt (_, attrs)
  | Cil.TFloat (_, attrs) -> attrs
  | Cil.TPtr (t, attrs)
  | Cil.TArray (t, _, attrs) -> collect_attributes t @ attrs
  | Cil.TFun (_, _, _, attrs) -> attrs
  | Cil.TNamed ({ Cil.ttype = t }, attrs) -> collect_attributes t @ attrs
  | Cil.TComp ({ Cil.cattr = attrs' }, attrs) -> attrs @ attrs'
  | Cil.TEnum (_, attrs) -> attrs
  | Cil.TBuiltin_va_list attrs -> failwith "va_list not implemented"

let is_pointer = function
  | Cil.TPtr (_, _) -> true
  | _ -> false

let contains_global =
  List.exists (function Cil.Attr (name, _) -> name = "global")

let contains_shared =
  List.exists (function Cil.Attr (name, _) -> name = "shared")

(*
At this moment we treat pointers as special;
we assume all pointers point to global memory which is the head of
some 1-dim array.
Maybe what is special is not a pointer, but a parameter of a kernel.
which has uniform value despite it is local.
If a parameter has a pointer type, the argument points to global memory.
 *)

let memory_kind_of_type t =
  let attrs = collect_attributes t in
  if is_pointer t then Global (* assume a pointer points to a global array *)
  else if contains_global attrs then Global
  else if contains_shared attrs then Shared
  else Local

exception CannotConvertCilTypeToWhy3Type of Cil.typ

let translate_type t =
  let rec transl t n = match t with
    | Cil.TVoid _ -> ty_unit, n
    | Cil.TInt (_, _) -> ty_int, n
    | Cil.TFloat (_, _) -> ty_real, n
    | Cil.TPtr (t, _) 
    | Cil.TArray (t, _, _) ->
       (* regard a pointer as an array *)
       transl t (n + 1)
    (* | TFun (t, args, vararg, attrs) -> *)
    (*    t_const "fun", attrs *)
    (* | TNamed ({ tname = name; ttype = ty; }, attrs) -> *)
    (*    let _, attrs' = translate_type ty in *)
    (*    t_const name, attrs @ attrs' *)
    (* | TComp (cinfo, attrs) -> *)
    (*    t_const ("struct " ^ cinfo.cname), attrs @ cinfo.cattr *)
    (* | TEnum (einfo, attrs) -> *)
    (*    t_const ("enum " ^ einfo.ename), attrs *)
    (* | TBuiltin_va_list attrs -> failwith "va_list not implemented" *)
    | t -> raise (CannotConvertCilTypeToWhy3Type t)
  in
  let ty, n = transl t 0 in
  ty_map (Why3.Ty.ty_tuple (List.make n ty_int)) ty

let register_vinfo vmap vinfo is_formal =
  let vtype = vinfo.Cil.vtype in
  let ty =
    if is_formal then translate_type vtype
    else ty_of_kind (memory_kind_of_type vtype) (translate_type vtype) in
  let k = if is_formal && not (is_pointer vtype) then Formal
          else memory_kind_of_type vinfo.Cil.vtype in
  let ls = create_ls vinfo.Cil.vname (Some ty) in
  let result = (k, ls) in
  (* debug "registering %s %s of type @[%a@]...@."
   *       (if k = Formal then "formal parameter" else "variable")
   *       vinfo.Cil.vname Why3.Pretty.print_ty ty; *)
  VarinfoMap.add vinfo result vmap

let lookup_vinfo vmap vinfo =
  (* debug "looking up %s...@." vinfo.Cil.vname; *)
  VarinfoMap.find vinfo vmap

let register_global_vars vmap file =
  let f vmap = function
    | Cil.GVarDecl (vinfo, _)
    | Cil.GVar (vinfo, _, _) ->
       let name = vinfo.Cil.vname in
       begin
         match name with
         | "declare_precondition"
         | "declare_postcondition"
         | "declare_invariant"
         | "declare_logic_param"
         | "assert"
         | "__syncthreads"
         | "blockDim"           (* t_blockdim *)
         | "gridDim" -> vmap    (* t_griddim *)
         | "threadIdx" -> vmap  (* eliminated during translation *)
         (* register_special_const vinfo Local (ty_local ty_dim3) *)
         | "blockIdx" -> vmap   (* eliminated during translation *)
         (* register_special_const vinfo Shared (ty_shared ty_dim3) *)
         | _ ->
            begin try 
                register_vinfo vmap vinfo false
              with
              | CannotConvertCilTypeToWhy3Type t ->
                 warn "Cannot convert type of %s into why3 type: %s\n"
                      vinfo.Cil.vname (Pretty.sprint 80 (Cil.d_type () t));
                 vmap
            end
       end
    | _ -> vmap
  in List.fold_left f vmap file.Cil.globals

let register_vars_in_fdecl vmap fdecl =
  (* debug "@[formals:@ @["; *)
  (* List.iter (fun vinfo -> debug "%s(%d); " vinfo.Cil.vname vinfo.Cil.vid) formals; *)
  (* debug "@]@.@[locals:@ @["; *)
  (* List.iter (fun vinfo -> debug "%s(%d); " vinfo.Cil.vname vinfo.Cil.vid) locals; *)
  (* debug "@]@."; *)
  let register_formal vmap vinfo = register_vinfo vmap vinfo true in
  let register_slocal vmap vinfo = register_vinfo vmap vinfo false in
  let vmap' = List.fold_left register_formal vmap fdecl.Cil.sformals in
  List.fold_left register_slocal vmap' fdecl.Cil.slocals

let make_initial_vmap file fdecl =
  let glob_vmap = register_global_vars VarinfoMap.empty file in
  register_vars_in_fdecl glob_vmap fdecl

(** cil exp -> why3 term ---------------- *)
let decompose_float x =
  assert (x >= 0.);
  let str = string_of_float x in
  let r = Str.regexp "\\([0-9]*\\)\\.\\([0-9]*\\)\\(e\\([-+]?[0-9]*\\)\\)?" in
  if Str.string_match r str 0 then
    (Str.matched_group 1 str,
     Str.matched_group 2 str,
     try Some (Str.matched_group 4 str) with Not_found -> None)
  else
    failwith @@ "failed to parse float: " ^ str
       
let translate_constant = function
  | Cil.CInt64 (n, k, s) ->
     t_const (Why3.Number.ConstInt (Why3.Number.int_const_dec (Int64.to_string n)))
  | Cil.CStr s ->
     failwith "cannot convert CStr to why3 term"
  | Cil.CWStr s ->
     failwith "cannot convert CWStr to why3 term"
  | Cil.CChr c ->
     t_nat_const (int_of_char c)
  | Cil.CReal (x, k, s) ->
     (* it seems impossible to create negative real constant in why3,
        so we first convert x's abs. value, and treat the sign later *)
     let is_minus = x < 0. in
     let i, f, e = decompose_float (abs_float x) in
     let t = t_const (Why3.Number.ConstReal (Why3.Number.real_const_dec i f e)) in
     if is_minus then t_real_uminus t else t
  | Cil.CEnum (e, s, i) ->
     failwith "cannot convert CEnum to why3 term"

let apply_unop op t : term =
  match op with
  | Cil.Neg ->
    begin match t.t_ty with
          | None ->
             failwith "invalid argument: -, formula"
          | Some ty ->
             if ty = ty_int then t_uminus t
             else if ty = ty_real then t_real_uminus t
             else failwith "argument of unary - is neither int nor real"
    end
  | Cil.BNot ->
     failwith "bit operation not implemented: ~"
  | Cil.LNot -> t_not_simp t

let apply_binop op t1 t2 : term = match op with
  | Cil.PlusA -> t_plus t1 t2
  | Cil.PlusPI -> t_get1 t1 t1
  | Cil.IndexPI
  | Cil.MinusPI -> failwith "pointer arithmetic is not implemented"
  | Cil.MinusA -> t_minus t1 t2
  | Cil.MinusPP -> failwith "pointer minus pointer not implemented"
  | Cil.Mult -> t_mult t1 t2
  | Cil.Div -> t_div t1 t2
  | Cil.Mod -> t_mod t1 t2
  | Cil.Shiftlt
  | Cil.Shiftrt -> failwith "bit operations not implemented"
  | Cil.Lt -> t_lt t1 t2
  | Cil.Gt -> t_gt t1 t2
  | Cil.Le -> t_le t1 t2
  | Cil.Ge -> t_ge t1 t2
  | Cil.Eq -> t_eq t1 t2
  | Cil.Ne -> t_ne t1 t2
  | Cil.BAnd
  | Cil.BXor
  | Cil.BOr -> failwith "bit operations not implemented"
  | Cil.LAnd -> t_and t1 t2
  | Cil.LOr -> t_or t1 t2

let rec translate_exp e vmap texp : term = match e with
  | Cil.Const c -> translate_constant c
  | Cil.Lval (lh, o) -> translate_lval lh o vmap texp
  | Cil.SizeOf ty -> failwith "sizeof not implemented"
  | Cil.SizeOfE e' -> failwith "sizeofE not implemented"
  | Cil.SizeOfStr s -> failwith "sizeofstr not implemented"
  | Cil.AlignOf t -> failwith "alignof not implemented"
  | Cil.AlignOfE e' -> failwith "alignofE not implemented"
  | Cil.UnOp (op, e', t) ->
     apply_unop op (translate_exp e' vmap texp)
  | Cil.BinOp (op, e1, e2, t) ->
     apply_binop op (translate_exp e1 vmap texp) (translate_exp e2 vmap texp)
  | Cil.Question (e1, e2, e3, t) ->
     t_if (translate_exp e1 vmap texp)
          (translate_exp e2 vmap texp)
          (translate_exp e3 vmap texp)
  | Cil.CastE (t, e') ->
     begin match t with
           | Cil.TFloat _ -> coerce_to_real @@ translate_exp e' vmap texp
           | _ ->
              (* return e' itself for a moment *)
              translate_exp e' vmap texp
     end
  | Cil.AddrOf lv -> failwith "addrof not implemented"
  | Cil.AddrOfLabel sref -> failwith "addroflabel not implemented"
  | Cil.StartOf lv -> failwith "startof not implemented"
and translate_lval lhost offset vmap texp : term =
  match lhost with
  | Cil.Var vinfo ->
     begin
       match vinfo.Cil.vname with
       | "threadIdx" -> translate_proj (t_tid_of texp) offset
       | "blockIdx" -> translate_proj (t_bid_of texp) offset
       | "blockDim" -> translate_proj t_bdim offset
       | "gridDim" -> translate_proj t_gdim offset
       | _ ->
          let (k, ls) = lookup_vinfo vmap vinfo in
          let base =
            match k with
            | Local -> t_acc_local (t_app ls [] ls.ls_value) texp
            | Shared -> t_acc_shared (t_app ls [] ls.ls_value) texp
            | Global -> t_acc_global (t_app ls [] ls.ls_value) texp
            | Formal -> t_app ls [] ls.ls_value
          (* the case vinfo is a formal? *)
          in t_get base (t_tuple (translate_offset offset vmap texp))
     end
  | Cil.Mem (Cil.BinOp ((Cil.PlusPI|Cil.IndexPI),
                        Cil.Lval (Cil.Var vinfo, Cil.NoOffset),
                        e, Cil.TPtr _)) ->
     (* x[e] matches this pattern if x is a pointer;
        in which case we assume x points to global memory.
        Probably in this case offset is empty? *)
     let (_, ls) = lookup_vinfo vmap vinfo in
     let ts = translate_offset offset vmap texp in
     t_get (t_app ls [] ls.ls_value) (t_tuple (translate_exp e vmap texp :: ts))
  | Cil.Mem _ ->
     failwith "Mem of this form is not implemented"
and translate_proj base offset = match offset with
  | Cil.NoOffset -> base
  | Cil.Field ({Cil.fname = "x"}, Cil.NoOffset) -> t_x base
  | Cil.Field ({Cil.fname = "y"}, Cil.NoOffset) -> t_y base
  | Cil.Field ({Cil.fname = "z"}, Cil.NoOffset) -> t_z base
  | Cil.Field ({Cil.fname = name}, _) ->
     failwith ("cannot translate access to the field " ^ name)
  | Cil.Index _ ->
     implementation_error "special constant followed by an index"
and translate_offset offset vmap texp = match offset with
  | Cil.NoOffset -> []
  | Cil.Field (f, o) ->
     failwith "cannot translate field access to why3 term"
  | Cil.Index (i, o) ->
     translate_exp i vmap texp :: translate_offset o vmap texp


(** program --> vc(s) ---------------- *)

type vcg_config = {
  c_mask : term -> term;
  c_vmap : (Formula.var_kind * lsymbol) VarinfoMap.t;
  c_lcmap : term list;
  c_logic : lsymbol StrMap.t;
  (* c_asgn : assignment_info list; *)
  c_decls : declaration list;
  c_vcs : vc list;
  (* c_check_race : bool; *)
  (* c_check_diverge : bool; *)
}

let make_initial_decls vmap preconds =
  List.map (fun c -> AxiomDecl c) preconds
  @ VarinfoMap.fold (fun _ (_, ls) acc -> VarDecl ls :: acc) vmap []

let make_vc ?name c goal =
  let decls = c.c_decls @ List.map (fun (_, ls) -> VarDecl ls)
                                   (StrMap.bindings c.c_logic)
  in
  { vc_decls = decls; vc_goal = goal; vc_name = name }

let add_vc ?name c goal =
  { c with c_vcs = make_vc ?name c goal :: c.c_vcs }


let rec translate_indices o vmap texp : term list = match o with
  | Cil.NoOffset -> []
  | Cil.Field (f, o) ->
     failwith "field access on the lhs of assignment is not supported"
  | Cil.Index (i, o) -> translate_exp i vmap texp :: translate_indices o vmap texp

let parse_formula str mask vmap log lcmap =
  debug "parsing formula %s@." str;
  let tbl = VarinfoMap.fold
              (fun vinfo (k, ls) l ->
               (vinfo.Cil.vname, (Some k, t_app ls [] ls.ls_value))
               :: l)
              vmap []
            @ StrMap.fold
                (fun name ls l ->
                 (name, (None, t_app ls [] ls.ls_value)) :: l)
                log []
            @ List.mapi (fun n t ->
                         (("loop_count" ^
                             if n = 0 then "" else "_" ^ string_of_int (n + 1)),
                          (None, t)))
                        lcmap in
  let vs = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in
  let fml = translate mask (t_var vs) tbl @@
              Fparser.expr Flexer.main @@ Lexing.from_string str in
  (if t_v_occurs vs fml > 0 then t_forall_threads vs [] fml else fml)
  |> fun x -> debug "done.@."; x

let transform_instr instr c = match instr with
  | Cil.Set ((lh, o), e, _) ->
     begin match lh with
           | Cil.Var vinfo ->
              (* var := e *)
              let (k, ls) = lookup_vinfo c.c_vmap vinfo in
              (* Fresh variable corresponding to the new value of [vinfo]. *)
              let k' = if k = Formal then Local else k in
              let ty = match ls.ls_value with
                | Some ty -> if k = Formal then ty_local ty else ty
                | None -> implementation_error
                            "logic variable with type formula"
              in
              let ls' = create_ls vinfo.Cil.vname (Some ty) in
              let vmap' = VarinfoMap.add vinfo (k', ls') c.c_vmap in
              let decls' = VarDecl ls' :: c.c_decls in
              let idxs t = t_tuple (translate_indices o c.c_vmap t) in
              let rhs = translate_exp e c.c_vmap in
              let a = { a_newvar = ls'; a_oldvar = ls; a_mkind = k;
                        a_mask = c.c_mask; a_index = idxs; a_rhs = rhs } in
              { c with (* c_asgn = a :: c.c_asgn; *) c_vmap = vmap';
                       c_decls = AsgnDecl a :: decls' }
           | Cil.Mem (Cil.BinOp ((Cil.PlusPI|Cil.IndexPI),
                                 Cil.Lval (Cil.Var vinfo, Cil.NoOffset),
                                 i, Cil.TPtr _)) ->
              (* var[i] := e *)
              assert (o = Cil.NoOffset);
              let (k, ls) = lookup_vinfo c.c_vmap vinfo in
              let ls' = create_ls vinfo.Cil.vname ls.ls_value in
              let vmap' = VarinfoMap.add vinfo (k, ls') c.c_vmap in
              let decls' = VarDecl ls' :: c.c_decls in
              let idxs t = t_tuple [translate_exp i c.c_vmap t] in
              let rhs = translate_exp e c.c_vmap in
              let a = { a_newvar = ls'; a_oldvar = ls; a_mkind = k;
                        a_mask = c.c_mask; a_index = idxs; a_rhs = rhs } in
              { c with (* c_asgn = a :: c.c_asgn; *) c_vmap = vmap';
                       c_decls = AsgnDecl a :: decls' }
           | Cil.Mem _ ->
              failwith @@ "cannot handle lval: " ^
                            (Pretty.sprint 80 (Cil.d_lval () (lh, o)))
     end
  | Cil.Call (None, Cil.Lval (Cil.Var {Cil.vname = "assert"},
                              Cil.NoOffset),
              args, _) ->
     let assertions =
       List.fold_left (fun ts arg ->
                       match arg with
                       | Cil.Const (Cil.CStr str) ->
                          parse_formula str c.c_mask c.c_vmap c.c_logic c.c_lcmap :: ts
                       | _ ->
                          warn "invlid assertion: not a string, ignored";
                          ts) [] args
     in
     let add_assertion c a =
       let c' = add_vc c a in
       { c' with c_decls = AxiomDecl a :: c.c_decls } in
     List.fold_left add_assertion c assertions
  | Cil.Call (None, Cil.Lval (Cil.Var {Cil.vname = "__syncthreads"},
                              Cil.NoOffset),
              args, _) ->
     if !Options.check_barrier_divergence then
       let vs = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in
       add_vc c (t_forall_threads vs [] (c.c_mask (t_var vs)))
     else c
  | Cil.Call (_, _, _, _) ->
     (* ignore function calls *)
     c
  | Cil.Asm _ -> not_implemented "cannot handle assembly"


let transform_instrs instrs c =
  List.fold_left (fun c instr ->
                  debug "generating wlp of instr @[%s@]@."
                        (Pretty.sprint 80 (Cil.d_instr () instr));
                  transform_instr instr c)
                 c instrs

(* --> cil.ml l.3858- *)
let rec skip_empty = function
    [] -> []
  | {Cil.skind=Cil.Instr []; Cil.labels=[]} :: rest -> skip_empty rest
  | x -> x

let find_while_pattern b =
  match skip_empty b.Cil.bstmts with
    {Cil.skind=Cil.If(e,tb,fb,_); Cil.labels=[]} :: rest ->
    begin
      match skip_empty tb.Cil.bstmts, skip_empty fb.Cil.bstmts with
        [], {Cil.skind=Cil.Break _; Cil.labels=[]} :: _  -> e, rest
      | {Cil.skind=Cil.Break _; Cil.labels=[]} :: _, []
        -> Cil.UnOp(Cil.LNot, e, Cil.intType), rest
      | _ -> raise Not_found
    end
  | _ -> raise Not_found
(* <-- *)

let rec find_call name = function
  | [] -> None
  | { Cil.skind = Cil.Instr [] } :: rest -> find_call name rest
  | { Cil.skind = Cil.Instr is } :: rest ->
     begin try
         Some (List.find
                 (function
                   | Cil.Call (None, Cil.Lval (Cil.Var vinfo, Cil.NoOffset), _, _) ->
                      vinfo.Cil.vname = name
                   | _ -> false)
                 is)
       with Not_found -> find_call name rest
     end
  | { Cil.skind = Cil.Block b } :: _ -> find_call name b.Cil.bstmts
  | _ -> None

let find_spec stmts keyword ?(mask=(fun _ -> t_true)) vmap log lcmap =
  match find_call keyword stmts with
  | Some (Cil.Call (_, _, args, _)) ->
     List.map (function
                | Cil.Const (Cil.CStr str) ->
                   parse_formula str mask vmap log lcmap
                | _ -> warn "invalid specification"; t_true)
              args
  | Some _ -> impl_error ""
  | None -> []

let find_invariants stmts mask =
  find_spec stmts ~mask "declare_invariant"

let find_preconditions stmts =
  find_spec stmts "declare_precondition"

let find_postconditions stmts =
  find_spec stmts "declare_postcondition"

let parse_declarator str =
  if Str.string_match (Str.regexp "\\([^][]+\\)\\(\\(\\[\\]\\)*\\)$") str 0
  then
    let name = Str.matched_group 1 str in
    let k = (String.length (Str.matched_group 2 str)) / 2 in
    Some (name, k)
  else
    (warn "invalid variable delcarator: %s" str; None)

let make_logic_param_list ty declarators =
  List.fold_left (fun m d ->
                  match parse_declarator d with
                  | None -> m
                  | Some (name, k) ->
                     if k = 0 then
                       StrMap.add name (create_ls name (Some ty)) m
                     else
                       let ty = ty_map (Why3.Ty.ty_tuple (List.make k ty_int)) ty in
                       StrMap.add name (create_ls name (Some ty)) m)
                 StrMap.empty
  @@ declarators

let parse_logic_params str =
  match Str.split (Str.regexp "[ ,;]+") str with
  | [] -> warn "invalid declaration: %s" str; None
  | tystr :: declarators ->
     match tystr with
     | "int" ->
        Some (make_logic_param_list ty_int declarators)
     | "float"
     | "real" ->
        Some (make_logic_param_list ty_real declarators)
     | _ ->
        warn "invalid type specification: %s" tystr;
        None

let find_logic_params stmts =
  match find_call "declare_logic_param" stmts with
  | Some (Cil.Call (_, _, args, _)) ->
     List.fold_left
       (fun m arg ->
        match arg with
        | Cil.Const (Cil.CStr str) ->
           begin
             match parse_logic_params str with
             | None -> m
             | Some m' ->
                StrMap.merge (fun name ls ls' ->
                              match ls, ls' with
                              | None, _ -> ls'
                              | _, None -> ls
                              | Some ls, Some ls' ->
                                 warn "duplicated declaration of parameter %s@."
                                      ls.ls_name.Why3.Ident.id_string;
                                 Some ls')
                             m m'
           end
        | _ ->
           warn "invalid logic parameter declaration";
           m)
       StrMap.empty args
  | Some _ -> impl_error "find_call returns an instruction that is not \
                          a function call"
  | None -> StrMap.empty

let rec find_modified s =
  let rec find vs stmt =
    match stmt with
    | Cil.Instr instrs ->
       List.fold_left find_i vs instrs
    | Cil.Return _ -> vs
    | Cil.Goto (_, _)
    | Cil.ComputedGoto (_, _) -> not_implemented "ComputedGoto"
    | Cil.Break _ -> not_implemented "Break statement"
    | Cil.Continue _ -> not_implemented "Continue statement"
    | Cil.If (e, b1, b2, _) ->
       let vs' = find_b vs b1 in find_b vs' b2
    | Cil.Switch (e, b, ss, _) -> not_implemented "Switch statement"
    | Cil.Loop (b, _, _, _) ->
       let _, bodystmts =
         try find_while_pattern b
         with Not_found -> not_implemented "General loop"
       in
       find_ss vs (List.map (fun s -> s.Cil.skind) bodystmts)
    | Cil.Block b -> find_b vs b
    | Cil.TryFinally _
    | Cil.TryExcept _ -> not_implemented "TryFinally/Except"
  and find_b vs b =
    find_ss vs (List.map (fun s -> s.Cil.skind) b.Cil.bstmts)
  and find_ss vs ss =
    List.fold_left (fun vs stmt -> find vs stmt) vs ss
  and find_i vs i =
    match i with
    | Cil.Set ((lh, o), _, _) ->
       begin
         match lh with
         | Cil.Var vinfo -> VarinfoMap.add vinfo () vs
         | Cil.Mem (Cil.BinOp ((Cil.PlusPI|Cil.IndexPI),
                                 Cil.Lval (Cil.Var vinfo, Cil.NoOffset),
                                 i, Cil.TPtr _)) ->
            VarinfoMap.add vinfo () vs
         | Cil.Mem _ ->
            failwith @@ "cannot handle lval: " ^
                          (Pretty.sprint 80 (Cil.d_lval () (lh, o)))
       end
    | Cil.Call _ ->
       (* ignore function calls; *)
       vs
    | Cil.Asm _ -> not_implemented "cannot handle assembly"
  in List.map fst @@ VarinfoMap.bindings @@ find VarinfoMap.empty s


let rec transform_stmt s c = match s with
  | Cil.Instr instrs -> transform_instrs instrs c
  | Cil.Return (None, _) -> c (* ? not very sure *)
  | Cil.Return (Some _, _) -> not_implemented "Return value"
  | Cil.Goto (_, _)
  | Cil.ComputedGoto (_, _) -> not_implemented "Goto statement"
  | Cil.Break _ -> not_implemented "Break statement"
  | Cil.Continue _ -> not_implemented "Continue statement"
  | Cil.If (e, b1, b2, _) ->
     let m = c.c_mask in
     let m1 t = t_and_simp (m t) (translate_exp e c.c_vmap t) in
     let m2 t = t_and_simp (m t) (t_not (translate_exp e c.c_vmap t)) in
     let c1 = transform_block b1 { c with c_mask = m1 } in
     let c2 = transform_block b2 { c1 with c_mask = m2 } in
     (* we have to restore the original mask *)
     { c2 with c_mask = m }
  | Cil.Switch (e, b, ss, _) -> not_implemented "Switch statement"
  | Cil.Loop (b, _, _, _) ->
     let e, bodystmts =
       try find_while_pattern b
       with Not_found -> not_implemented "General loop"
     in
     (* [invs] is a function that receives mask, vmap and lcmap, and
      * returns a list of declared invariants. *)
     let invs = find_invariants bodystmts in
     (* VCs for loop entry: each invariant has to hold at loop entry,
      * so a goal is generated for each declared invariant. *)
     let vcs1 = List.map (make_vc ~name:"loop_entry" c)
                         (invs (fun t ->
                                t_and_simp (c.c_mask t) (translate_exp e c.c_vmap t))
                               c.c_vmap c.c_logic
                               (t_zero :: c.c_lcmap)) in
     (* [vars_mod] is a list of variables that may be modified
      * during each execution of the loop body *)
     let vars_mod = List.concat @@
                      List.map (fun s -> find_modified s.Cil.skind)
                               bodystmts in
     (* Alist whose entry is a pair of ls's, representing old and new
      * values of a variable in [vars_mod].
      * Fresh ls is generated for each variable.  *)
     let ls_alist =
       List.map (fun vinfo ->
                 let (_, ls) = lookup_vinfo c.c_vmap vinfo in
                 ls, create_ls vinfo.Cil.vname ls.ls_value)
                vars_mod in
     (* new map from vinfo to ls representing vinfo's new value  *)
     let vmap' = List.fold_left2 (fun vm vinfo (_, ls) ->
                                  let (k, _) = lookup_vinfo c.c_vmap vinfo in
                                  VarinfoMap.add vinfo (k, ls) vm)
                                 c.c_vmap vars_mod ls_alist in
     let l_lc = create_ls "lc" (Some ty_int) in
     let lcmap' = t_ls l_lc :: c.c_lcmap in
     (* mask for the next iteration *)
     let mask' t = t_and_simp (c.c_mask t) (translate_exp e vmap' t) in
     (* declaration list extended by fresh ls's generated above, plus
      * assumption that invariants hold at the beginning of the loop.
      * Also we can assume that the loop counter is not negative. *)
     let decls' =
       VarDecl l_lc
       :: AxiomDecl (t_le t_zero (t_ls l_lc))
       :: List.map (fun t -> AxiomDecl t) (invs mask' vmap' c.c_logic lcmap')
       @ List.map (fun (_, ls) -> VarDecl ls) ls_alist
       @ c.c_decls in
     (* Another side condition: invariants have to be invariant indeed.
      * This condition is obtained by first executing
      * the body, obtaining [c''], and then asserting that the invariants
      * hold under [c''], with the loop counter being incremented by one.
      * Here we rely on the assumption that the loop is monotonic,
      * since we re-use [mask'] as a state of mask during iterations.  *)
     let vcs2 =
       (* We have to add an assumption that the mask is not empty. *)
       let decls'' =
         let vs = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in 
         AxiomDecl (t_exists_threads vs [] (mask' (t_var vs))) :: decls'
       in
       (* Use [vmap'] and [decls''] to make a new configuration
        * corresponding to the state after several (possebly 0)
        * iterations.  Also, mask is updated on each iteration, so
        * change [c_mask] appropriately. *)
       let c' = { c with c_vmap = vmap'; c_decls = decls'';
                         c_lcmap = lcmap'; c_mask = mask'; }
       in
       let c'' = transform_stmts 
                   (List.map (fun s -> s.Cil.skind) bodystmts)
                   c'
       in
       let mask'' t = t_and_simp (c.c_mask t) (translate_exp e c''.c_vmap t) in
       let lcmap'' = t_plus (t_ls l_lc) (t_nat_const 1) :: c.c_lcmap in
       List.map (fun t -> make_vc ~name:"invariant_preservation" c'' t)
                (invs mask'' c''.c_vmap c.c_logic lcmap'')
       @ c''.c_vcs
     in
     (* After exiting the loop, the invariants are still true, and
      * additionally the guard is false on all enabled threads.
      * We have to add an axiom expressing the latter. *)
     let decls'' =
       let vs = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in
       let t = t_forall_threads vs [] @@
                 t_not (t_and (c.c_mask (t_var vs))
                              (translate_exp e vmap' (t_var vs))) in
       AxiomDecl t :: decls' in
     { c with c_vmap = vmap'; c_decls = decls'';
              c_vcs = vcs2 @ vcs1; }
  | Cil.Block b -> transform_block b c
  | Cil.TryFinally _
  | Cil.TryExcept _ -> not_implemented "TryFinally/Except"
and transform_block b c =
  transform_stmts (List.map (fun s -> s.Cil.skind) b.Cil.bstmts) c
and transform_stmts ss c =
  List.fold_left (fun c stmt -> transform_stmt stmt c) c ss

let generate_vc file fdecl =
  let vmap = make_initial_vmap file fdecl in
  let body = fdecl.Cil.sbody in
  let log = find_logic_params body.Cil.bstmts in
  let pre = find_preconditions body.Cil.bstmts vmap log [] in
  let decls = make_initial_decls vmap pre in
  let c = 
    { c_mask = Formula.t_is_valid_thread; c_vmap = vmap;
      c_lcmap = []; c_logic = log;
      c_decls = decls; c_vcs = []; } in
  debug "generating vc for %s..." fdecl.Cil.svar.Cil.vname;
  let c' = transform_block body c in
  let post = find_postconditions body.Cil.bstmts c'.c_vmap log [] in
  let vcs = List.map (make_vc c') post @ c'.c_vcs in
  debug "generated vc.\n";
  vcs
