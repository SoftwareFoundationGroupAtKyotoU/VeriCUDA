open Why3.Term
open Why3api

(* ---------------- calling provers *)
(* Why3 manual says we just write
   [Whyconf.prover_by_id config "alt-ergo"]
   but this function doesn't seem to exist in version 0.86. *)
let find_prover config name =
  let prover = Why3.Stdlib.Mstr.find name @@
                 Why3.Whyconf.get_prover_shortcuts config
  in
  Why3.Whyconf.Mprover.find prover @@ Why3.Whyconf.get_provers config

(* Try to prove task [task] using theorem prover named [prover]. *)
let prove_task prover ?(timelimit=10) ?(memlimit=4000) task =
  let p = find_prover config prover in
  let driver =
    Why3.Driver.load_driver env p.Why3.Whyconf.driver [] in
  Why3.Driver.prove_task
    ~command:p.Why3.Whyconf.command
    ~limit:(Why3.Call_provers.mk_limit timelimit memlimit (-1))
    driver
    task

let output_coq_of_task dir task =
  let p = find_prover config "coq" in
  let driver = Why3.Driver.load_driver env p.Why3.Whyconf.driver [] in
  let cout = open_out (Filename.concat dir ("task" ^ string_of_int (Why3.Task.task_hash task) ^ ".v")) in
  Why3.Driver.print_task driver (Format.formatter_of_out_channel cout) task

module I = Why3.BigInt
open Formula
open Utils

(* ---------------- polynomial over terms *)
module OrderedTerm : Polynomial.OrderedType with type t = term = struct
  type t = term
  let compare = t_compare
end

module PTerm =  Polynomial.Make(OrderedTerm)
open PTerm

let rec to_polynomial t : polynomial =
  match t.t_ty with
  | Some ty when Why3.Ty.ty_equal ty ty_int ->
     begin
       match t.t_node with
       | Tvar _ -> p_var t
       | Tconst (Why3.Number.ConstInt i) ->
          p_bigint (Why3.Number.compute_int i)
       | Tapp (op, [t1; t2]) ->
          if ls_equal op fs_plus then
            p_add (to_polynomial t1) (to_polynomial t2)
          else if ls_equal op fs_minus then
            p_sub (to_polynomial t1) (to_polynomial t2)
          else if ls_equal op fs_mult then
            p_mult (to_polynomial t1) (to_polynomial t2)
          else
            p_var t
       | Tapp (op, [t1]) when ls_equal op fs_uminus ->
          p_neg (to_polynomial t1)
       | _ ->
          p_var t
     end
  | _ ->
     invalid_arg "to_polynomial, a term of type non-int"

(* let to_polynomial_memo = ref Mterm.empty
 * 
 * let to_polynomial t =
 *   try Mterm.find t !to_polynomial_memo
 *   with Not_found ->
 *        let p = to_polynomial t in
 *        to_polynomial_memo := Mterm.add t p !to_polynomial_memo;
 *        p *)

let rec from_polynomial p =
  p_fold (fun t -> t)
         (fun n ->
          let t = t_const @@
                    Why3.Number.ConstInt (
                        Why3.Number.int_const_dec (I.to_string (I.abs n)))
          in
          if I.lt n I.zero then t_uminus t else t)
         t_plus t_mult p

let rec isolate_var x p =
  (* Given a polynomial [p] and a variable [x],
   * returns a pair [(q, s)] such that p = s * x + q,
   * [q] does not contain x, and s = 1 or s = -1,
   * if such q, s exists.
   * 
   * If such a [q] exists, then necessarily q = p(x:=0).
   * So it suffices to check whether p - p(x:=0) equals
   * x or -x.
   *
   * BEWARE: this function does not check internal structure of
   * "variables", that is, if [p = x + p_var t] this function returns
   * [(p_var t, 1)] even if [x] occurs in [t]. *)
  (* debug "isolate_var receives %a@." Why3.Pretty.print_term (from_polynomial p); *)
  let q = p_subst x p_zero p in
  let p_q = p_sub p q in
  (* debug "removing %a, %a@."
   *       Why3.Pretty.print_term x
   *       Why3.Pretty.print_term (from_polynomial p_q); *)
  if p_equal (p_var x) p_q then Some (q, 1)
  else if p_equal (p_neg (p_var x)) p_q then Some (q, -1)
  else None


(* ---------------- manipulating/generating terms *)
let t_ls ls = t_app ls [] ls.ls_value

let rec t_replace_simp t1 t2 t =
  if t_equal t t1 then t2
  else t_map_simp (t_replace_simp t1 t2) t

let t_quant_close_guard q vsyms triggers guard body =
  match q with
  | Tforall ->
     t_forall_close_simp vsyms triggers @@ t_implies guard body
  | Texists ->
     t_exists_close_simp vsyms triggers @@ t_and guard body

let t_ls_occurs ls t = t_s_any (fun _ -> false) (ls_equal ls) t

let is_formula t = t.t_ty = None

let decompose_tuple t =
  match t.t_ty with
  | Some { Why3.Ty.ty_node = Why3.Ty.Tyapp (ts, tys) }
       when Why3.Ty.ts_equal ts (Why3.Ty.ts_tuple (List.length tys)) ->
     begin
       match t.t_node with
     | Tapp (fs, elts) when ls_equal fs (fs_tuple (List.length tys)) ->
        Some elts
     | _ -> None
     end
  | _ -> None

(* A function to make an equation specielized to tuples.  *)
let t_equ_tp tp1 tp2 =
  (* [tp1] and [tp2] must be tuples of the same size. *)
  match decompose_tuple tp1, decompose_tuple tp2 with
  | Some ts1, Some ts2 ->
     assert (List.length ts1 = List.length ts2);
     t_and_simp_l (List.map2 Why3.Term.t_equ_simp ts1 ts2)
  | _ ->
     debug "t_equ_tp (%a) (%a)@."
           Why3.Pretty.print_term tp1 Why3.Pretty.print_term tp2;
     implementation_error "t_equ_tp, not a tuple"

let is_int t = match t.t_ty with
  | None -> false
  | Some t -> Why3.Ty.ty_equal ty_int t

let is_cmp_op ls =
  ls_equal ls ps_equ
  || ls_equal ls ps_le
  || ls_equal ls ps_lt
  || ls_equal ls ps_ge
  || ls_equal ls ps_gt

let dim_const_list =
  [t_bdimx; t_bdimy; t_bdimz; t_gdimx; t_gdimy; t_gdimz]

let is_dim_const t = List.exists (t_equal t) dim_const_list

let is_int_const t =
  match t.t_node with
  | Tconst _ -> true
  | _ -> false

let is_dim_const_or_int_const t = is_dim_const t || is_int_const t

let is_dim_const_polynomial p =
  p_fold is_dim_const_or_int_const (fun _ -> true) (&&) (&&) p

(* Let p be a polynomial in variables x1, ..., xn.
 * We say p is semi-positive if all coefficients of the non-constant terms
 * of p are positive.
 * We say p is semi-negative if -p is semi-positive.
 *
 * Let p be a semi-positive polynomial.
 * We want to know whether 0 <= p for all positive values of x's.
 * Obviously, 0 <= p for all positive x's if and only if
 * 0 <= p(1, ..., 1). *)

let is_semi_positive p =
  let r = p_repr p in
  List.for_all (fun (m, n) -> m = [] || I.ge n I.zero) r

let is_semi_negative p =
  let r = p_repr p in
  List.for_all (fun (m, n) -> m = [] || I.le n I.zero) r

let eval_polynomial p =
  p_fold (fun _ -> I.one) (fun n -> n) I.add I.mul p

let rec remove_trivial_comparison t =
  match t.t_node with
  | Tapp (ls, [t1; t2]) when is_int t1 && is_cmp_op ls ->
     let p = p_sub (to_polynomial t1) (to_polynomial t2) in
     if p_is_const p then
       let n = p_const_part p in
       if
         (* p <ls> 0? *)
         ls_equal ls ps_lt && I.lt n I.zero
         || ls_equal ls ps_le && I.le n I.zero
         || ls_equal ls ps_gt && I.gt n I.zero
         || ls_equal ls ps_ge && I.ge n I.zero
         || ls_equal ls ps_equ && I.eq n I.zero
       then t_true
       else t_false
     else if is_dim_const_polynomial p then
       if
         (* p < 0 if p is semi-negative and p(1, ..., 1) < 0 *)
         ls_equal ls ps_lt && is_semi_negative p &&
           I.lt (eval_polynomial p) I.zero
         (* p <= 0 if p is semi-negative and p(1, ..., 1) <= 0 *)
         || ls_equal ls ps_le && is_semi_negative p &&
              I.le (eval_polynomial p) I.zero
         || ls_equal ls ps_gt && is_semi_positive p &&
              I.gt (eval_polynomial p) I.zero
         || ls_equal ls ps_ge && is_semi_positive p &&
              I.ge (eval_polynomial p) I.zero
       then t_true
       else t
     else t
  | _ -> TermTF.t_map_simp (fun t -> t) remove_trivial_comparison t

(* Shadows Why3.Term.t_equ_simp. *)
let rec t_equ_simp t1 t2 =
  match decompose_tuple t1, decompose_tuple t2 with
  | Some ts1, Some ts2 ->
     assert (List.length ts1 = List.length ts2);
     t_and_simp_l (List.map2 t_equ_simp ts1 ts2)
  | Some _, None
  | None, Some _ ->  Why3.Term.t_equ_simp t1 t2
  | None, None ->
     match t1.t_node, t2.t_node, t1.t_ty with
     | Teps _, Teps _, Some { Why3.Ty.ty_node =
                                Why3.Ty.Tyapp (_, [ty; _]) } ->
        let vs = create_vsymbol (Why3.Ident.id_fresh "arg") ty in
        t_forall_close_simp [vs] [] @@
          t_equ (t_func_app t1 (t_var vs)) (t_func_app t2 (t_var vs))
     (* | Teps tb1, Teps tb2 ->
      *    
      *    let (vs1, t1'), (vs2, t2') = t_open_bound tb1, t_open_bound tb2 in
      *    debug "epsilon %a. %a@."
      *          Why3.Pretty.print_vs vs1 Why3.Pretty.print_term t1';
      *    debug "epsilon %a. %a@."
      *          Why3.Pretty.print_vs vs2 Why3.Pretty.print_term t2';
      *    t_forall_close_simp [vs1] [] @@
      *      t_equ_simp t1' (t_subst_single vs2 (t_var vs1) t2') *)
     | _ when is_int t1 ->
        remove_trivial_comparison @@ Why3.Term.t_equ t1 t2
     | _ -> Why3.Term.t_equ_simp t1 t2

let t_neq_tp tp1 tp2 = t_not_simp (t_equ_tp tp1 tp2)

let is_tautology t =
  t_equal t_true @@ t_map_simp (fun t -> t) t

let rec is_pos t =
  (* Returns [Some true] if [t] is definitely positive,
   * [Some false] if [t] is not positive.
   * Returns [None] if it fails to determine the sign of [t].  *)
  if is_dim_const t then
    Some true
  else
    match t.t_node with
    | Tconst (Why3.Number.ConstInt i) ->
       begin
         match I.sign (Why3.Number.compute_int i) with
         | 1 -> Some true
         | _ -> Some false
       end
    | Tapp (ls, [t1; t2]) when ls_equal ls fs_mult ->
       begin
         match is_pos t1, is_pos t2 with
         | Some b1, Some b2 -> Some (b1 = b2)
         | _, _ -> None
       end
    | _ -> None

let t_pos t =
  (* Returns a formula that is equivalent to [0 < t]. *)
  match is_pos t with
  | Some true -> t_true
  | Some false -> t_false
  | None -> t_lt t_zero t

let t_size t =
  let rec f n t = match t.Why3.Term.t_node with
    | Why3.Term.Tvar _
    | Why3.Term.Tconst _
    | Why3.Term.Ttrue
    | Why3.Term.Tfalse -> n + 1
    | _ -> Why3.Term.t_fold f (n + 1) t
  in
  f 0 t


(** ---------------- simplification *)
let rec collect_conjuncts t =
  match t.t_node with
  | Tbinop (Tand, t1, t2) ->
     collect_conjuncts t1 @ collect_conjuncts t2
  | _ -> [t]

let rec simplify_guards t =
  match t.t_node with
  | Tbinop ((Timplies | Tand) as op, t1, t2) ->
     let t1' = simplify_guards t1 in
     collect_conjuncts t1'
     |> List.fold_left
          (fun t guard ->
           match guard.t_node with
           | Tnot guard' -> t_replace_simp guard' t_false t
           | _ -> t_replace_simp guard t_true t)
          t2
     |> simplify_guards
     |> t_binary_simp op t1'
  | Tbinop (Tor, t1, t2) ->
     let t1' = simplify_guards t1 in
     let t2' = simplify_guards t2 in
     begin
       match t1'.t_node with
       | Tnot t1'' ->
          let t2'' = t_replace_simp t1'' t_true t2' in
          t_or_simp t1' t2''
       | _ ->
          let t2'' = t_replace_simp t1' t_false t2' in
          t_or_simp t1' t2''
     end
  | _ -> t_map_simp simplify_guards t

let rec compute_thread_projections t =
  match t.t_node with
  (* bid_of (b, t) --> b *)
  | Tapp (ls, [{ t_node = Tapp (ls', [t1; _]) }])
       when ls_equal ls fs_bid_of && ls_equal ls' (fs_tuple 2)
    -> t1
  (* tid_of (b, t) --> t *)
  | Tapp (ls, [{ t_node = Tapp (ls', [_; t2]) }])
       when ls_equal ls fs_tid_of && ls_equal ls' (fs_tuple 2)
    -> t2
  (* x { a; b; c } --> a *)
  | Tapp (ls, [{ t_node = Tapp (ls', [t1; _; _]) }])
       when ls_equal ls fs_x && ls_equal ls' fs_mk_dim3
    -> t1
  (* y { a; b; c } --> b *)
  | Tapp (ls, [{ t_node = Tapp (ls', [_; t2; _]) }])
       when ls_equal ls fs_y && ls_equal ls' fs_mk_dim3
    -> t2
  (* z { a; b; c } --> c *)
  | Tapp (ls, [{ t_node = Tapp (ls', [_; _; t3]) }])
       when ls_equal ls fs_z && ls_equal ls' fs_mk_dim3
    -> t3
  | _ ->
     t_map_simp compute_thread_projections t

let rec simplify_dim3_equality t =
  match t.t_node with
  | Tapp (ls, [ { t_node = Tapp (ls1, [x; y; z]) };
                { t_node = Tapp (ls2, [x'; y'; z'])} ])
       when ls_equal ls ps_equ &&
              ls_equal ls1 fs_mk_dim3 && ls_equal ls2 fs_mk_dim3 ->
     t_and_simp_l [t_equ_simp x x'; t_equ_simp y y'; t_equ_simp z z']
  | _ -> t_map_simp simplify_dim3_equality t

let rec simplify_formula t =
  simplify_guards t
  |> compute_thread_projections
  |> simplify_dim3_equality
  |> remove_trivial_comparison


(* ---------------- manitpulating tasks *)
let rec task_map_decl f task =
  match task with
  | None -> None
  | Some {
        Why3.Task.task_decl = tdecl;
        Why3.Task.task_prev = task_prev;
      } ->
     match tdecl.Why3.Theory.td_node with
     | Why3.Theory.Decl {
         Why3.Decl.d_node = Why3.Decl.Dprop (k, pr, t)
       }
          when k = Why3.Decl.Pgoal ||
                 let name = pr.Why3.Decl.pr_name.Why3.Ident.id_string in
                 Str.string_match (Str.regexp "^vc_premise_") name 0
       ->
        let t' = f t in
        if k == Why3.Decl.Paxiom && is_tautology t' then
          task_map_decl f task_prev
        else
          Why3.Task.add_decl (task_map_decl f task_prev)
                             (Why3.Decl.create_prop_decl k pr t')
     | _ ->
        Why3.Task.add_tdecl (task_map_decl f task_prev) tdecl

let apply_why3trans trans task =
  Why3.Trans.apply_transform trans env task

(* apply [fn] to the goal of [task] *)
let transform_goal fn task =
  let goal, task' = Why3.Task.task_separate_goal task in
  Why3.Task.add_decl task' @@
    Why3.Decl.create_prop_decl Why3.Decl.Pgoal
                               (Why3.Task.task_goal task) @@
      (fn (Why3.Task.task_goal_fmla task))

