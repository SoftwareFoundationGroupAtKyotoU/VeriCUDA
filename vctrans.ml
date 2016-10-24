(*
 #use "topfind";;
 #directory "/home/kozima/.opam/4.01.0/lib/menhirLib";;
 #load "menhirLib.cmo";;
 #require "why3";;
 #require "cil";;
*)

open Why3.Term
open Why3api
open Formula
open Vc
open Utils
open ExtList

module I = Why3.BigInt

open Why3util
open Why3util.PTerm

(** ---------------- simplification *)
(* let rec collect_conjuncts t =
 *   match t.t_node with
 *   | Tbinop (Tand, t1, t2) ->
 *      collect_conjuncts t1 @ collect_conjuncts t2
 *   | _ -> [t]
 * 
 * let rec simplify_guards t =
 *   match t.t_node with
 *   | Tbinop ((Timplies | Tand) as op, t1, t2) ->
 *      let t1' = simplify_guards t1 in
 *      collect_conjuncts t1'
 *      |> List.fold_left
 *           (fun t guard ->
 *            match guard.t_node with
 *            | Tnot guard' -> t_replace_simp guard' t_false t
 *            | _ -> t_replace_simp guard t_true t)
 *           t2
 *      |> simplify_guards
 *      |> t_binary_simp op t1'
 *   | Tbinop (Tor, t1, t2) ->
 *      let t1' = simplify_guards t1 in
 *      let t2' = simplify_guards t2 in
 *      begin
 *        match t1'.t_node with
 *        | Tnot t1'' ->
 *           let t2'' = t_replace_simp t1'' t_true t2' in
 *           t_or_simp t1' t2''
 *        | _ ->
 *           let t2'' = t_replace_simp t1' t_false t2' in
 *           t_or_simp t1' t2''
 *      end
 *   | _ -> t_map_simp simplify_guards t
 * 
 * let rec compute_thread_projections t =
 *   match t.t_node with
 *   (\* bid_of (b, t) --> b *\)
 *   | Tapp (ls, [{ t_node = Tapp (ls', [t1; _]) }])
 *        when ls_equal ls fs_bid_of && ls_equal ls' (fs_tuple 2)
 *     -> t1
 *   (\* tid_of (b, t) --> t *\)
 *   | Tapp (ls, [{ t_node = Tapp (ls', [_; t2]) }])
 *        when ls_equal ls fs_tid_of && ls_equal ls' (fs_tuple 2)
 *     -> t2
 *   (\* x { a; b; c } --> a *\)
 *   | Tapp (ls, [{ t_node = Tapp (ls', [t1; _; _]) }])
 *        when ls_equal ls fs_x && ls_equal ls' fs_mk_dim3
 *     -> t1
 *   (\* y { a; b; c } --> b *\)
 *   | Tapp (ls, [{ t_node = Tapp (ls', [_; t2; _]) }])
 *        when ls_equal ls fs_y && ls_equal ls' fs_mk_dim3
 *     -> t2
 *   (\* z { a; b; c } --> c *\)
 *   | Tapp (ls, [{ t_node = Tapp (ls', [_; _; t3]) }])
 *        when ls_equal ls fs_z && ls_equal ls' fs_mk_dim3
 *     -> t3
 *   | _ ->
 *      t_map_simp compute_thread_projections t
 * 
 * let rec simplify_dim3_equality t =
 *   match t.t_node with
 *   | Tapp (ls, [ { t_node = Tapp (ls1, [x; y; z]) };
 *                 { t_node = Tapp (ls2, [x'; y'; z'])} ])
 *        when ls_equal ls ps_equ &&
 *               ls_equal ls1 fs_mk_dim3 && ls_equal ls2 fs_mk_dim3 ->
 *      t_and_simp_l [t_equ_simp x x'; t_equ_simp y y'; t_equ_simp z z']
 *   | _ -> t_map_simp simplify_dim3_equality t
 * 
 * let rec simplify_formula t =
 *   simplify_guards t
 *   |> compute_thread_projections
 *   |> simplify_dim3_equality
 *   |> remove_trivial_comparison *)



(** ---------------- Decompose quantifications over thread  *)
let t_is_valid_tid_inline t =
  let zero = t_zero in
  t_and_simp_l [
      t_le zero (t_x t); t_le zero (t_y t); t_le zero (t_z t);
      t_lt (t_x t) t_bdimx; t_lt (t_y t) t_bdimy; t_lt (t_z t) t_bdimz;
    ]

let t_is_valid_bid_inline t =
  let zero = t_zero in
  t_and_simp_l [
      t_le zero (t_x t); t_le zero (t_y t); t_le zero (t_z t);
      t_lt (t_x t) t_gdimx; t_lt (t_y t) t_gdimy; t_lt (t_z t) t_gdimz;
    ]

let rec inline_is_valid_thread t =
  match t.t_node with
  | Tapp (ls, [t']) when ls_equal ls ps_is_valid_thread ->
     begin
       match t'.t_node with
       | Tapp (ls, [t1; t2]) when ls_equal ls (fs_tuple 2) ->
          t_and_simp (t_is_valid_bid_inline t1) (t_is_valid_tid_inline t2)
       | _ ->
          TermTF.t_map_simp (fun t -> t) inline_is_valid_thread t
     end
  | _ ->
     TermTF.t_map_simp (fun t -> t) inline_is_valid_thread t

let decomposing_quant q vss body =
  let rec rewrite_body vss acc_vs body =
    match vss with
    | [] -> acc_vs, body
    | vs::vss' ->
       if Why3.Ty.ty_equal vs.vs_ty ty_thread then
         let bx = create_vsymbol (Why3.Ident.id_fresh "b_x") ty_int in
         let by = create_vsymbol (Why3.Ident.id_fresh "b_y") ty_int in
         let bz = create_vsymbol (Why3.Ident.id_fresh "b_z") ty_int in
         let tx = create_vsymbol (Why3.Ident.id_fresh "t_x") ty_int in
         let ty = create_vsymbol (Why3.Ident.id_fresh "t_y") ty_int in
         let tz = create_vsymbol (Why3.Ident.id_fresh "t_z") ty_int in
         let th = t_tuple [t_dim3 (t_var bx) (t_var by) (t_var bz);
                           t_dim3 (t_var tx) (t_var ty) (t_var tz)]
         in
         t_subst_single vs th body
         |> inline_is_valid_thread
         |> compute_thread_projections
         |> simplify_formula
         |> simplify_dim3_equality
         |> rewrite_body vss' (bx :: tx :: by :: ty :: bz :: tz :: acc_vs)
       else if Why3.Ty.ty_equal vs.vs_ty ty_dim3 then
         let x = create_vsymbol (Why3.Ident.id_fresh "d_x") ty_int in
         let y = create_vsymbol (Why3.Ident.id_fresh "d_y") ty_int in
         let z = create_vsymbol (Why3.Ident.id_fresh "d_z") ty_int in
         let d = t_dim3 (t_var x) (t_var y) (t_var z) in
         t_subst_single vs d body
         |> inline_is_valid_thread
         |> compute_thread_projections
         |> simplify_formula
         |> simplify_dim3_equality
         |> rewrite_body vss' (x :: y :: z :: acc_vs)
       else
         rewrite_body vss' (vs :: acc_vs) body
  in
  let (vss, body) = rewrite_body vss [] body in
  t_quant_close_simp q vss [] body

let rec decompose_thread_quant t =
  match t.t_node with
  | Tquant (q, tq) ->
     let (vss, tr, body) = t_open_quant tq in
     (* decompose only when there is no trigger *)
     if tr = [] &&
          List.exists (fun vs ->
                       Why3.Ty.ty_equal vs.vs_ty ty_thread
                       || Why3.Ty.ty_equal vs.vs_ty ty_dim3) vss then
       decomposing_quant q vss @@ decompose_thread_quant body
     else
       TermTF.t_map_simp (fun t -> t) decompose_thread_quant t
  | _ -> TermTF.t_map_simp (fun t -> t) decompose_thread_quant t

(* let decompose_thread_quant t =
 *   let t' = decompose_thread_quant t in
 *   if not (t_equal t t_false) && t_equal t' t_false then
 *     (debug "%a@.-->@.%a@." Why3.Pretty.print_term t
 *            Why3.Pretty.print_term t';
 *      exit 0);
 *   t' *)


(** ---------------- eliminating quantifiers *)

(* maybe optimizable using a method similar to
 * why3-0.85/src/transform/simplify_formula.ml,
 * find the value [s], substitute to [vs] in the whole formula,
 * and then simplify it modulo ring equality using polynomial repr. above. *)
let rec eliminate_unique_quant_1 bvars sign vs t =
  (* Try to find the value of [vs] if it is unique in [t].
   * If the value is found, returns a pair [t'] and [Some s]
   * where [s] is the value, and [t'] is [t(vs:=s)]. *)
  match t.t_node with
  | Tapp (ls, [t1; t2])
       when sign && ls_equal ls ps_equ && is_int t1 &&
              Mvs.set_disjoint (t_vars t) bvars ->
     begin 
       match isolate_var (t_var vs)
                         (p_sub (to_polynomial t1) (to_polynomial t2))
       with
       | None -> (t, None)
       | Some (p, _) when t_v_occurs vs (from_polynomial p) > 0 -> (t, None)
       | Some (p, s) ->
          (* t1 - t2 = s * x + p (= 0)
           * ==> x = -s * p *)
          let p' = if s = 1 then (p_neg p) else p in
          (t_true, Some (from_polynomial p'))
     end
  | Tbinop (Tor, t1, t2) when not sign ->
     let (t1', r1) = eliminate_unique_quant_1 bvars sign vs t1 in
     begin
       match r1 with
       | None ->
          assert (t_equal t1 t1');
          let (t2', r2) = eliminate_unique_quant_1 bvars sign vs t2 in
          begin
            match r2 with
            | None ->
               assert (t_equal t2 t2');
               (t, None)
            | Some s -> (t_or_simp (t_subst_single vs s t1) t2', r2)
          end
       | Some s ->
          (t_or_simp t1' (t_subst_single vs s t2), r1)
     end
  | Tbinop (Tand, t1, t2) when sign ->
     let (t1', r1) = eliminate_unique_quant_1 bvars sign vs t1 in
     begin
       match r1 with
       | None ->
          assert (t_equal t1 t1');
          let (t2', r2) = eliminate_unique_quant_1 bvars sign vs t2 in
          begin
            match r2 with
            | None ->
               assert (t_equal t2 t2');
               (t, None)
            | Some s ->
               (t_and_simp (t_subst_single vs s t1) t2', r2)
          end
       | Some s ->
          (t_and_simp t1' (t_subst_single vs s t2), r1)
     end
  | Tbinop (Timplies, t1, t2) when not sign ->
     let (t1', r1) = eliminate_unique_quant_1 bvars (not sign) vs t1 in
     begin
       match r1 with
       | None ->
          assert (t_equal t1 t1');
          let (t2', r2) = eliminate_unique_quant_1 bvars sign vs t2 in
          begin
            match r2 with
            | None ->
               assert (t_equal t2 t2');
               (t, None)
            | Some s ->
               (t_implies_simp (t_subst_single vs s t1) t2', r2)
          end
       | Some s ->
          (t_implies_simp t1' (t_subst_single vs s t2), r1)
     end
  | Tnot t' ->
     let (t'', r) = eliminate_unique_quant_1 bvars (not sign) vs t' in
     t_not_simp t'', r
  | Tquant (q, tq) ->
     let (vsyms, triggers, body, cb) = t_open_quant_cb tq in
     let bvars' = List.fold_left (fun bvs v -> Mvs.add v 1 bvs) bvars vsyms in
     let (t', r) = eliminate_unique_quant_1 bvars' sign vs body in
     t_quant q (cb vsyms triggers t'), r
  | _ -> (t, None)

let rec eliminate_unique_quant t =
  match t.t_node with
  | Tquant (q, tq) ->
     begin
       match t_open_quant tq with
       | (vss, [], body) ->
          let sign = match q with Tforall -> false | Texists -> true in
          let rec elim vss vss_rem t =
            match vss with
            | [] -> t_quant_close_simp q vss_rem [] t
            | vs :: vss' ->
               let (t', r) = eliminate_unique_quant_1 Mvs.empty sign vs t in
               match r with
               | None ->
                  assert (t_equal t t');
                  elim vss' (vs :: vss_rem) t'
               | Some _ ->
                  elim vss' vss_rem t'
          in elim vss [] @@ eliminate_unique_quant body
       | (vsyms, triggers, body) ->
          t_quant_close q vsyms triggers (eliminate_unique_quant body)
     end
  | _ -> TermTF.t_map_simp (fun t -> t) eliminate_unique_quant t


(** ---------------- merging quantifiers *)
(* Try to find a subformula equivalent to either
 *   forall x y. 0 <= x < a -> 0 <= y < b -> P (x + a * y)
 *   exists x y. 0 <= x < a /\ 0 <= y < b /\ P (x + a * y)
 * and replace it with
 *   a <= 0 \/ b <= 0 \/ forall z. 0 <= z < a * b -> P z
 *   a > 0 /\ b > 0 /\ exists z. 0 <= z < a * b /\ P z
 * respectively. *)

(* A (node of a) term is said to be a polynomial node if
 * - it is of type int, and
 * - it is either variable, integer constant or an application whose
 *   operator is one of the ring operations. *)
let is_polynomial_node t =
  match t.t_node with
  | Tvar vs -> Why3.Ty.ty_equal vs.vs_ty ty_int
  | Tconst (Why3.Number.ConstInt _) -> true
  | Tapp (ls, _) ->
     ls_equal ls fs_plus
     || ls_equal ls fs_minus
     || ls_equal ls fs_mult
     || ls_equal ls fs_uminus
  | _ -> false
      
(* We call a subterm [p] of [t] a prime polynomial node if
 * - [p] is a polynomial node, and
 * -- either [p = t], or
 * -- the parent node of [p] is not a polynomial node. *)

exception CannotReduceVariables

(* FIXME: this doesn't seem to work if t is not affine in x, y *)
let really_process_polynomial x a y z t =
  (* [t] is a prime polynomial node of the formula in question. *)
  let p = to_polynomial t in
  (* Given p(a, x, y), a polynomial in a, x, and y,
   * returns a function f that receives [z] and returns a polynomial
   * g(a, z) such that g(a, x + a * y) = p(a, x, y).
   * If there is no such f, returns [None]. *)
  (* debug "Processing polynomial with %a, %a, %a:@.  @[%a@]...@."
   *       Why3.Pretty.print_term x
   *       Why3.Pretty.print_term a
   *       Why3.Pretty.print_term y
   *       Why3.Pretty.print_term t; *)
  let p_a = to_polynomial a in
  let p_y = to_polynomial y in
  if p_contains y (p_subst x (p_neg (p_mult p_a p_y)) p)
  then raise CannotReduceVariables
  else from_polynomial @@ p_subst x (p_var z) (p_subst y p_zero p)

let process_polynomial x a y z t =
  let rec f p t =
    (* Apply [really_process_polynomial] to every prime polynomial
     * node of [t].  Parameter [p] is true iff the parent of the
     * argument [t] is a polynomial (in particular [t] is not a root). *)
    if is_polynomial_node t then
      let t' = t_map_simp (f true) t in
      if p then t' else really_process_polynomial x a y z t'
    else t_map_simp (f false) t
  in f false t

let rec try_reduce_vars x a y z t =
  match t.t_node with
  | Tvar _ -> if t_equal t x || t_equal t y
              then raise CannotReduceVariables
              else t
  | Tapp (ls, [t1; t2]) when is_int t1 && is_cmp_op ls ->
     let t' = process_polynomial x a y z (t_minus t1 t2) in
     t_app ls [t'; t_zero] None
  | Tapp (ls, ts) ->
     if is_formula t then t_map_simp (try_reduce_vars x a y z) t
     else process_polynomial x a y z t
  | _ ->
     t_map_simp (try_reduce_vars x a y z) t

let reduce_variables q vs1 bound1 vs2 bound2 t =
  assert (is_formula t);
  let new_vs = create_vsymbol (Why3.Ident.id_fresh "z") ty_int in
  let v1 = t_var vs1 in
  let v2 = t_var vs2 in
  let v = t_var new_vs in
  try
    let t' = try_reduce_vars v1 bound1 v2 v t in new_vs, t'
  with CannotReduceVariables ->
    let t' = try_reduce_vars v2 bound2 v1 v t in new_vs, t'

let check_lower_bound q v t =
  (* Returns [t'] such that
   * when [q] is [Texists], [t] iff [0 <= v /\ t'], and
   * when [q] is [Tforall], [t] iff [0 <= v -> t'].
   * 
   * This function actually finds a subformula equivalent to [0 <= v]
   * in appropriate positions, and replaces such subformulas with [true].
   *)
  let check_cmp pos ls t1 t2 =
    let p = p_sub (to_polynomial t1) (to_polynomial t2) in
    match isolate_var v p with
    | Some (q, 1) ->
       (* p = x + q, therefore [x <ls> -q]. *)
       if pos then
         (* is [x <ls> -q] equivalent to [x >= 0]? *)
         ls_equal ls ps_ge && p_equal q p_zero
         || ls_equal ls ps_gt && p_equal q (p_int 1)
       else
         (* is [x <ls> -q] equivalent to [x < 0]? *)
         ls_equal ls ps_le && p_equal q (p_int 1)
         || ls_equal ls ps_lt && p_equal q p_zero
    | Some (q, s) ->
       assert (s = -1);
       (* p = -x + q, therefore [q <ls> x]. *)
       if pos then
         (* is [q <ls> x] equivalent to [x >= 0]? *)
         ls_equal ls ps_le && p_equal q p_zero
         || ls_equal ls ps_lt && p_equal q (p_int (-1))
       else
         (* is [q <ls> x] equivalent to [x < 0]? *)
         ls_equal ls ps_ge && p_equal q (p_int (-1))
         || ls_equal ls ps_gt && p_equal q p_zero
    | None -> false
  in
  let rec check pos t =
    match t.t_node with
    | Tapp (ls, [t1; t2]) when is_int t1 && is_cmp_op ls ->
       check_cmp pos ls t1 t2
    | Tbinop (Tand, t1, t2) ->
       if pos then
         (* does [t1 /\ t2] imply [0 < v]? *)
         check pos t1 || check pos t2
       else
         (* does [v < 0] imply [t1 /\ t2]? *)
         check pos t1 && check pos t2
    | Tbinop (Tor, t1, t2) ->
       if pos then
         check pos t1 && check pos t2
       else
         check pos t1 || check pos t2
    | Tbinop (Timplies, t1, t2) ->
       if pos then
         check (not pos) t1 && check pos t2
       else
         check (not pos) t1 || check pos t2
    | Tbinop (Tiff, t1, t2) ->
       check pos (t_and (t_implies t1 t2) (t_implies t2 t1))
    | Tnot t' ->
       check (not pos) t'
    | Tquant (q, tq) ->
       (* Here we are assuming that the domain of quantification
        * is always non-empty.  *)
       let (_, _, t') = t_open_quant tq in
       check pos t'
    | _ ->
       (* Ignore let, case, eps, etc. *)
       false
  in check (q = Texists) t

let find_upper_bounds q v t =
  (* Returns the set of [u]'s such that:
   * when [q] is [Texists], [t] implies [v < u], and
   * when [q] is [Tforall], [t] is implied by [v >= u].
   *)
  let rec find pos t =
    match t.t_node with
    | Tapp (ls, [t1; t2]) when is_int t1 && is_cmp_op ls ->
       let p = p_sub (to_polynomial t1) (to_polynomial t2) in
       begin
         match isolate_var v p with
         | Some (q, 1) ->
            if pos then        (* want: [v < u] for some u *)
              (* p = v + q, therefore [x <ls> -q]. *)
              if ls_equal ls ps_le then
                (* v <= -q, hence v < -q + 1 *)
                Sterm.singleton (from_polynomial (p_add (p_int 1) (p_neg q)))
              else if ls_equal ls ps_lt then
                (* v < -q *)
                Sterm.singleton (from_polynomial (p_neg q))
              else 
                Sterm.empty
            else                (* want: [v >= u] for some u *)
              if ls_equal ls ps_ge then
                (* v >= -q *)
                Sterm.singleton (from_polynomial (p_neg q))
              else if ls_equal ls ps_gt then
                (* v > -q, hence v >= -q + 1 *)
                Sterm.singleton (from_polynomial (p_add (p_int 1) (p_neg q)))
              else
                Sterm.empty
         | Some (q, s) ->
            assert (s = -1);
            if pos then        (* want: [v < u] for some u *)
              (* p = -v + q, therefore [q <ls> v]. *)
              if ls_equal ls ps_ge then
                (* q >= v, hence v < q + 1 *)
                Sterm.singleton (from_polynomial (p_add (p_int 1) q))
              else if ls_equal ls ps_gt then
                (* q > v *)
                Sterm.singleton (from_polynomial q)
              else 
                Sterm.empty
            else                (* want: [v >= u] for some u *)
              if ls_equal ls ps_le then
                (* q <= v *)
                Sterm.singleton (from_polynomial q)
              else if ls_equal ls ps_lt then
                (* q < v, hence q + 1 < v *)
                Sterm.singleton (from_polynomial (p_add (p_int 1) q))
              else
                Sterm.empty
         | None -> Sterm.empty
       end
    | Tbinop (Tand, t1, t2) -> 
       if pos then
         Sterm.union (find pos t1) (find pos t2)
       else
         Sterm.inter (find pos t1) (find pos t2)
    | Tbinop (Tor, t1, t2) ->
       if pos then
         Sterm.inter (find pos t1) (find pos t2)
       else
         Sterm.union (find pos t1) (find pos t2)
    | Tbinop (Timplies, t1, t2) ->
       if pos then
         Sterm.inter (find (not pos) t1) (find pos t2)
       else
         Sterm.union (find (not pos) t1) (find pos t2)
    | Tnot t' ->
       find (not pos) t'
    | Tquant (q, tq) ->
       let (_, _, t') = t_open_quant tq in
       find pos t'
    | _ -> Sterm.empty
  in find (q = Texists) t

let polynomial_of_inequality ls t1 t2 =
  (* returns a polynomial [p] such that [t1 <ls> t2] iff [0 < p]. *)
  let p1, p2 = to_polynomial t1, to_polynomial t2 in
  if ls_equal ls ps_le then
    (* [t1 <= t2] iff [0 < t2 - t1 + 1] *)
    p_add (p_sub p2 p1) (p_int 1)
  else if ls_equal ls ps_lt then
    (* [t1 < t2] iff [0 < t2 - t1] *)
    p_sub p2 p1
  else if ls_equal ls ps_ge then
    (* [t1 >= t2] iff [0 < t1 - t2 + 1 ] *)
    p_add (p_sub p1 p2) (p_int 1)
  else if ls_equal ls ps_gt then
    (* [t1 > t2] iff [0 < t1 - t2] *)
    p_sub p2 p1
  else
    implementation_error "invalid argument to polynomial_of_inequality"

let replace_guard_formula vs u t =
  (* replace (as many as possible) subformulas of [t] with [true]
   * which are implied by [0 <= vs < u]. *)
  let p1 = polynomial_of_inequality ps_le t_zero (t_var vs) in
  let p2 = polynomial_of_inequality ps_lt (t_var vs) u in
  let is_non_negative p = p_is_const p && I.le I.zero (p_const_part p) in
  let rec replace t =
    match t.t_node with
    | Tapp (ls, [t1; t2]) when is_int t1 && is_cmp_op ls &&
                                 not @@ ls_equal ls ps_equ ->
       let p = polynomial_of_inequality ls t1 t2 in
       (* We have to check [0 < p] implies either [0 < p1] or [0 < p2].
        * Either [p <= p1] or [p <= p2] is sufficient (but not necessary).
        * We simply check that either [p1 - p] or [p2 - p] is a non-negative
        * constant. *)
       if is_non_negative (p_sub p1 p) || is_non_negative (p_sub p2 p)
       then t_true
       else t
    | _ ->
       TermTF.t_map_simp (fun t -> t) replace t
  in replace t

let rec merge_quantifiers t =
  match t.t_node with
  | Tquant (q, _) ->
     (* Separate [t] into a list of quantified variables,
      * a list of guards, and a body.
      * [t] is logically equivalent to
      * [t_quant_close_guard q vss [] (t_and_simp_l gs) b].  *)
     let vss, gs, b =
       (* Guards are accumulated in the reverse order;
        * but there is no strong reason for doing so. *)
       let rec separate q qvss gs t =
         match t.t_node with
         | Tquant (q', tq) when q = q' ->
            (* triggers are removed here (any problem?) *)
            let (vss, _, t') = t_open_quant tq in
            separate q (qvss @ vss) gs t'
         | Tbinop (op, t1, t2)
              when (q = Tforall && op = Timplies) ||
                     (q = Texists && op = Tand)
           -> separate q qvss (t1 :: gs) t2
         | _ ->
            qvss, gs, t
       in
       separate q [] [] t
     in
     (* Merge inner quantifiers first;
      * [t] is equivalent to [t_quant_close q vss [] t'] *)
     let gs' = List.rev_map merge_quantifiers gs in
     let b' = merge_quantifiers b in
     let t' =
       match q with
       | Tforall -> t_implies_simp (t_and_simp_l gs') b'
       | Texists -> t_and_simp (t_and_simp_l gs') b'
     in
     (* Partition [vss] into two; bounded and unbounded ones.
      * Bounded variables should essentially be guarded by [0 <= x < u]
      * for some term [u], otherwise a variable is considered unbounded.
      * [vs_ub_list] is a list of bounded variables each of which is
      * associated with its upper bound, and [vs_nb] consists of unbounded
      * ones. *)
     let vs_ub_list, vs_nb =
       List.fold_left (fun (b, nb) vs ->
                       if check_lower_bound q (t_var vs) t' then
                         let ubs = Sterm.elements @@
                                     find_upper_bounds q (t_var vs) t'
                                   |> List.filter (fun ub ->
                                                   t_v_occurs vs ub = 0)
                         in
                         if ubs = [] then b, vs :: nb
                         else (vs, ubs) :: b, nb
                       else b, vs :: nb)
                      ([], []) (List.rev vss)
     in
     let merge'' q vs ub vs' ub' t =
       assert (t_v_occurs vs ub = 0);
       assert (t_v_occurs vs' ub' = 0);
       if  t_v_occurs vs' ub = 0 && t_v_occurs vs ub' = 0 then
         try
           let vs_new, t' = reduce_variables q vs ub vs' ub' t in
           Some (vs_new, vs, vs', ub, ub', t')
         with CannotReduceVariables -> None
       else None
     in
     let rec merge' vs ub l t =
       match l with
       | [] -> None
       | (vs', ubs') :: l' ->
          try Some (List.find_map (fun ub' ->
                                   merge'' q vs ub vs' ub' @@
                                     replace_guard_formula vs' ub' t)
                                  ubs')
          with Not_found -> merge' vs ub l' t
     in
     let rec merge l t =
       match l with
       | [] | [_] -> None
       | (vs, ubs) :: l' ->
          try Some (List.find_map (fun ub ->
                                   merge' vs ub l' @@
                                     replace_guard_formula vs ub t)
                                  ubs)
          with Not_found -> merge l' t
     in
     (* Merge as many variables from [list] as possible, and returns
      * the resulting formula and a list of variables used in it
      * (both newly introduced ones and the ones that were not merged). *)
     let rec merge_all list t =
       match merge list t with
       | Some (vs_new, vs, vs', ub, ub', t') ->
          (* Found a pair to be merged. *)
          (* [vs] and [vs'] are to be eliminated; they should not
           * appear in the formula we are going to return, which is
           * built from [t'], [ub], and [ub']. *)
          assert (t_v_occurs vs t' = 0);
          assert (t_v_occurs vs' t' = 0);
          assert (List.exists (fun (vs'', _) -> vs_equal vs'' vs) list);
          assert (List.exists (fun (vs'', _) -> vs_equal vs'' vs') list);
          (* Here [t] can be rewritten as (when [q] is [Tforall]):
           *   0 <= vs_new < ub * ub' -> t'
           * but the equivalence holds only if [ub] and [ub'] are positive.
           * So in general we need more complex form
           *   0 < ub /\ 0 < ub' /\ 0 <= vs_new < ub * ub' -> t'.
           * The case of [Texists] is similar.
           * Therefore the guard is
           *   0 < ub /\ 0 < ub' /\ 0 <= vs_new < ub * ub'.  *)
          let guard = t_and_simp_l [
                          t_pos ub;
                          t_pos ub';
                          t_le t_zero (t_var vs_new);
                          t_lt (t_var vs_new) (t_mult ub ub')]
                      |> remove_trivial_comparison
          in
          (* New list of variables, equipped with their upper bounds. *)
          let list' =
            (vs_new, [t_mult ub ub']) ::
              List.filter
                (fun (vs'', _) ->
                 not (vs_equal vs' vs'' || vs_equal vs vs''))
                list
          in
          (* Add the guard above to the body, and try to merge
           * remaining variables. *)
          merge_all list' @@
            if q = Tforall then
              t_implies_simp guard t'
            else
              t_and_simp guard t'
       | None ->
          (* no more pairs to be merged *)
          list, t
     in
     let list', t'' = merge_all vs_ub_list t' in
     if List.length list' < List.length vs_ub_list then
       (* [list'] has length fewer than the original list.
        * This means that some pair of variables are merged. *)
       t_quant_close_simp q (List.map fst list' @ vs_nb) [] t''
     else if List.for_all2 t_equal gs gs' && t_equal b b' then
       (* No variables are merged.  Return the original formula.  *)
       t
     else
       (* No variables among [vss] are merged, but the variables in
        * guards or body are merged.  *)
       t_quant_close_simp q vss [] t''
  | _ ->
     TermTF.t_map_simp (fun t -> t) merge_quantifiers t

let merge_quantifiers t =
  let t' = merge_quantifiers t in
  if not @@ t_equal t t' then
    debug "merge quantifiers: %a@. -->@.  %a@."
          Why3.Pretty.print_term t Why3.Pretty.print_term t'
  else
    debug "merge quantifiers fails: %a@."
          Why3.Pretty.print_term t;
  t'

(* let merge_quantifiers task =
 *   task_map_decl
 *     (fun t ->
 *      let t' = eliminate_unique_quant t
 *               |> merge_quantifiers_t
 *      in
 *      (\* if not (t_equal t t') then
 *       *   debug "eliminate_linear_quantifier turns@.  %a@.into@.  %a@."
 *       *         Why3.Pretty.print_term t Why3.Pretty.print_term t'; *\)
 *      t')
 *     task *)

(** ---------------- eliminate existentials in premises *)
let rec eliminate_existential_in_premises task =
  let destruct d = match d.Why3.Decl.d_node with
    | Why3.Decl.Dprop (k, pr, { t_node = Tquant (Texists, tq) }) ->
       begin
         match t_open_quant tq with
         | (vss, [], body) ->
            let alist =
              List.map (fun vs ->
                        let ls =
                          create_lsymbol
                            (Why3.Ident.id_clone vs.vs_name)
                            [] (Some vs.vs_ty) in
                        (vs, ls))
                       vss
            in
            let body' =
              List.fold_left (fun t (vs, ls) ->
                              t_subst_single vs (fs_app ls [] vs.vs_ty) t)
                             body alist
            in
            List.map (fun (_, ls) -> Why3.Decl.create_param_decl ls) alist @
              [Why3.Decl.create_prop_decl k pr body']
         | _ -> [d]
       end
    | _ -> [d]
  in
  Why3.Trans.apply (Why3.Trans.decl destruct None) task


(** ---------------- apply equalities in premises *)
type complex_eqn = {
  ce_vars : vsymbol list;
  ce_guards : term list;
  ce_ls : lsymbol;
  ce_args : term list;
  ce_rhs : term;
}

type simple_eqn = {
  se_ls : lsymbol;
  se_lhs : term;
  se_rhs : term;
}

type eqn =
  | SimpleEqn of simple_eqn
  | ComplexEqn of complex_eqn

type eqn_info = {
  ei_eqn : eqn;
  ei_ps : Why3.Decl.prsymbol;
}

let eqn_info_ls = function
  | { ei_eqn = SimpleEqn { se_ls = ls } }
  | { ei_eqn = ComplexEqn { ce_ls = ls } } -> ls

let print_complex_eqn fmt = function
    { ce_vars = vars;
      ce_guards = guards;
      ce_ls = ls;
      ce_args = args;
      ce_rhs = rhs; } ->
    Format.fprintf fmt
                   "@[{ ce_vars = %a;@.  \
                    ce_guards = %a;@.  \
                    ce_ls = %a;@.  \
                    ce_args = %a;@.  \
                    ce_rhs = %a; }@.@]"
                   (fun fmt vss ->
                    Format.fprintf fmt "[";
                    List.iter (Format.fprintf fmt "%a; " Why3.Pretty.print_vs)
                              vss;
                    Format.fprintf fmt "]")
                   vars
                   (fun fmt guards ->
                    Format.fprintf fmt "[";
                    List.iter (Format.fprintf fmt "%a; " Why3.Pretty.print_term)
                              guards;
                    Format.fprintf fmt "]")
                   guards
                   Why3.Pretty.print_ls
                   ls
                   (fun fmt guards ->
                    Format.fprintf fmt "[";
                    List.iter (Format.fprintf fmt "%a; " Why3.Pretty.print_term)
                              guards;
                    Format.fprintf fmt "]")
                   args
                   Why3.Pretty.print_term rhs

let rec extract_complex_eqn f =
  (* Extract complex_eqn from [f].
   * If [f] is of the form
   *   forall xs1. gs1 -> forall xs2. gs2 -> ... forall xsn. gsn ->
   *     ls[arg1][arg2]...[argm] = rhs
   * then returns
   * Some
   *   { ce_vars = xs1 @ xs2 @ ... @ xsn;
   *     ce_guards = [gs1; gs2; ...; gsn];
   *     ce_ls = ls; ce_args = [argm; ...; arg2; arg1];
   *     ce_rhs = rhs }. *)
  match f.t_node with
  | Tapp (ls, [lhs; rhs]) when ls_equal ps_equ ls ->
     let rec f t = match t.t_node with
       | Tapp (ls, []) -> Some (ls, [])
       | Tapp (ls, [t1; t2]) when ls_equal ls fs_get ->
          begin
            match f t1 with
            | Some (ls', args) -> Some (ls', t2 :: args)
            | None -> None
          end
       | _ -> None
     in
     begin
       match f lhs with
       | Some (ls, args) 
            (* To avoid infinite loop, make sure that [ls] does not
             * appear in the rhs. *)
            when t_s_any (fun _ -> true) (ls_equal ls) rhs ->
          Some { ce_vars = []; ce_guards = [];
                 ce_ls = ls; ce_args = args; ce_rhs = rhs; }
       | _ -> None
     end
  | Tbinop (Timplies, f1, f2) ->
     begin
       match extract_complex_eqn f2 with
       | Some e -> Some { e with ce_guards = f1 :: e.ce_guards }
       | None -> None
     end
  (* | Tbinop (Tand, f1, f2) ->
   *    merge (extract_ce_info f1) (extract_ce_info f2)
   * | Tbinop (Tiff, f1, f2) ->
   *    merge (f1, extract_ce_info f2) (f2, extract_ce_info f1) *)
  | Tquant (Tforall, tq) ->
     let (vss, tr, f') = t_open_quant tq in
     begin
       match extract_complex_eqn f' with
       | Some e -> Some { e with ce_vars = vss @ e.ce_vars; }
       | None -> None
     end
  | _ -> None

(* let extract_complex_eqn f =
 *   let result = extract_complex_eqn f in
 *   begin match result with
 *         | None -> ()
 *         | Some e ->
 *            debug "extracted eqn: @[%a@]@." print_complex_eqn e
 *   end;
 *   result *)

let is_wf_eqn = function
    { ce_vars = vars;
      ce_guards = guards;
      ce_ls = ls;
      ce_args = args;
      ce_rhs = rhs; } ->
    not (List.exists (t_ls_occurs ls) guards)

let extract_eqn t =
  match t.t_node with
  | Tapp (ls, [t1; t2]) when ls_equal ps_equ ls ->
     Some (SimpleEqn { se_ls = ls; se_lhs = t1; se_rhs = t2 })
  | _ -> match extract_complex_eqn t with
         | Some e -> if is_wf_eqn e then Some (ComplexEqn e) else None
         | None -> None

let collect_eqns task =
  List.filter_map (fun decl ->
                   match decl.Why3.Decl.d_node with
                   | Why3.Decl.Dprop (Why3.Decl.Paxiom, ps, t) ->
                      begin
                        match extract_eqn t with
                        | Some e -> Some { ei_eqn = e; ei_ps = ps }
                        | None -> None
                      end
                   | _ -> None)
                  (Why3.Task.task_decls task)

let collect_eqns_test task =
  let eqns = collect_eqns task in
  if eqns = [] then debug "No equations found@."
  else List.iter
         (function
           | { ei_eqn = SimpleEqn { se_lhs =lhs; se_rhs = rhs } } ->
              debug "Found equation: %a = %a@."
                    Why3.Pretty.print_term lhs
                    Why3.Pretty.print_term rhs
           | { ei_eqn =
                 ComplexEqn { ce_ls = ls; ce_args = args; ce_rhs = rhs; } } ->
              let lhs =
                List.fold_left t_get (t_app ls [] ls.ls_value)
                               (List.rev args)
              in 
              debug "Found equation: %a = %a@."
                    Why3.Pretty.print_term lhs
                    Why3.Pretty.print_term rhs)
         eqns

let rec match_lhs ls args t =
  (* If [args] is [a1; a2; ...; an], this function checkes whether
   * [t] has the form [get (... (get (get ls a1) a2) ...) an],
   * and returns the list of terms corresponding to [a1], [a2], ...,
   * [an] in the reverse order. *)
  match t.t_node, args with
  | Tapp (ls', []), [] when ls_equal ls ls' -> Some []
  | Tapp (ls', [t1; t2]), a::args' when ls_equal ls' fs_get ->
     begin
       match match_lhs ls args' t1 with
       | Some ts -> Some (t2 :: ts)
       | None -> None
     end
  | _ -> None

let rec find_match bvs ls args t =
  match match_lhs ls args t with
  | Some ts ->
     if Svs.exists (fun vs -> List.exists
                                (t_v_any (vs_equal vs)) ts)
                   bvs
     then
       (* At least one of [ts] contains a bound variable; reject. *)
       []
     else [(ts, t)]
  | None -> 
     match t.t_node with
     | Tquant (q, tq) ->
        let (vss, _, t') = t_open_quant tq in
        let bvs' = List.fold_right Svs.add vss bvs in
        find_match bvs' ls args t'
     | Teps b ->
        let (vs, t') = t_open_bound b in
        find_match (Svs.add vs bvs) ls args t'
     | Tlet (t1, b) ->
        let (vs, t2) = t_open_bound b in
        find_match bvs ls args t1
        @ find_match (Svs.add vs bvs) ls args t2
     | _ ->
        t_fold (fun acc t ->
                find_match bvs ls args t @ acc)
               [] t

let apply_simple_eqn { se_lhs = lhs; se_rhs = rhs } t =
  t_replace lhs rhs t

let rec t_map_on_quant f t =
  match t.t_node with
  | Tquant _ -> t_map_simp f t
  | _ -> t_map_simp (t_map_on_quant f) t

let rec apply_complex_eqn eqn seen t =
  if t_ls_occurs eqn.ce_ls t then
    match t.t_node with
    | Tbinop (op, t1, t2) when not (t_ls_occurs eqn.ce_ls t1) ->
       t_binary_simp op t1 (apply_complex_eqn eqn seen t2)
    | Tbinop (op, t1, t2) when not (t_ls_occurs eqn.ce_ls t2) ->
       t_binary_simp op (apply_complex_eqn eqn seen t1) t2
    | _ ->
       let matches = find_match Svs.empty eqn.ce_ls eqn.ce_args t
                     |> List.filter (fun (_, s) -> not (Sterm.mem s seen))
                     |> List.unique
                          ~cmp:(fun (ts, t) (ts', t') ->
                                if t_equal t t' then
                                  (assert (List.for_all2 t_equal ts ts'); true)
                                else false)
       in
       let seen' = List.fold_left
                     (fun seen (_, s) -> Sterm.add s seen)
                     seen matches
       in
       List.fold_left
         (fun t (ts, s) ->
          (* [t_occurs s t] is not necessarily true because of the
           * simplification. *)
          if t_occurs s t then
            (* debug "match found: %a@." Why3.Pretty.print_term s;
             * List.iter (fun t -> debug " list: %a@." Why3.Pretty.print_term t) ts;
             * List.iter (fun t -> debug " pattern: %a@." Why3.Pretty.print_term t) eqn.ce_args; *)
            t_or_simp
              (t_exists_close eqn.ce_vars [] @@
                 (t_and_simp_l [t_and_simp_l eqn.ce_guards;
                                t_and_simp_l (List.map2 t_equ_simp
                                                        eqn.ce_args ts);
                                t_replace s eqn.ce_rhs t]))
              (t_and_simp
                 (t_not_simp
                    (t_exists_close eqn.ce_vars [] @@
                       (t_and_simp (t_and_simp_l eqn.ce_guards)
                                   (t_and_simp_l (List.map2 t_equ_simp
                                                            eqn.ce_args ts)))))
                 t)
            |> simplify_formula
          else t)
         t matches
       |> t_map_on_quant (apply_complex_eqn eqn seen')
  else
    t

let apply_eqn_to_term e t =
  match e with
  | SimpleEqn e -> apply_simple_eqn e t
  | ComplexEqn e -> apply_complex_eqn e Sterm.empty t

(* let apply_eqn_to_term eqn t =
 *   debug "rewriting %a...@." Why3.Pretty.print_term t;
 *   let t' = apply_eqn_to_term eqn t in
 *   if not ( t_equal t t') then
 *     debug "rewrote into@.    @[%a@]@." Why3.Pretty.print_term t';
 *   t' *)
                                
(* let t_size t =
 *   let rec f n t =
 *     if is_formula t then
 *       t_fold f n t
 *     else
 *       n + 1
 *   in
 *   f 0 t
 * 
 * let apply_eqn_to_term eqn t =
 *   let size = t_size t in
 *   if size > 100 then (\* debug "%a@." Why3.Pretty.print_term t; *\)
 *     debug "apply_eqn_to_term(%d) @?" size;
 *   let t1 = Sys.time () in
 *   let y = apply_eqn_to_term eqn t in
 *   let t2 = Sys.time () in
 *   if size > 100 then debug "%f sec.@." (t2 -. t1);
 *   y *)

let rec apply_eqn_info task eqn_info =
  (* debug "apply_eqn_info %d@." (Why3.Task.task_hash task); *)
  match task with
  | None -> None
  | Some {
        Why3.Task.task_decl = tdecl;
        Why3.Task.task_prev = task_prev;
      } ->
     match tdecl.Why3.Theory.td_node with
     | Why3.Theory.Decl {
         Why3.Decl.d_node = Why3.Decl.Dprop (k, pr, t)
       } when not (Why3.Decl.pr_equal pr eqn_info.ei_ps) ->
        let task_prev' = apply_eqn_info task_prev eqn_info in
        let t' = apply_eqn_to_term eqn_info.ei_eqn t in
        if Why3.Task.task_equal task_prev task_prev' then
          (* There is no further occurrence of [lhs]. *)
          if t_equal t t' then
            (* There is no occurrence of [lhs] in [t], so we
             * just leave [task] unchanged. *)
            task
          else if k = Why3.Decl.Paxiom && is_tautology t' then
            (* Slight optimization to suppress trivial axioms. *)
            task_prev'
          else
            (* [lhs] occurs in [t], so we should replace it with [rhs].
             * Since this is the first occurrence of [lhs], we have to
             * declare lsymbols in [rhs] here. *)
            let lss = t_s_fold (fun s _ -> s)
                               (fun s ls -> Sls.add ls s)
                               Sls.empty t'
            in
            let task' =
              Sls.fold (fun ls task ->
                        let decl = Why3.Decl.create_param_decl ls in
                        try Why3.Task.add_decl task decl
                        with Why3.Decl.RedeclaredIdent _ -> task)
                       lss task_prev
            in
            let decl = Why3.Decl.create_prop_decl k pr t' in
            Why3.Task.add_decl task' decl
        else
          (* [lhs] occurs in [task_prev], so lsymbols inside [rhs] is
           * already declared in [task_prev']. *)
          if t_equal t t' then
            Why3.Task.add_tdecl task_prev' tdecl
          else if k = Why3.Decl.Paxiom && is_tautology t' then
            task_prev'
          else
            let decl = Why3.Decl.create_prop_decl k pr t' in
            Why3.Task.add_decl task_prev' decl
     | Why3.Theory.Decl {
           Why3.Decl.d_node = Why3.Decl.Dparam ls
         } ->
        if ls_equal ls (eqn_info_ls eqn_info) then
          (* Nothing more to be rewritten. *)
          task
        else
          let task_prev' = apply_eqn_info task_prev eqn_info in
          if Why3.Task.task_equal task_prev task_prev' then
            (* There is no further occurrence of [lhs].
             * No changes needed. *)
            task
          else
            (* There is an occurence of [lhs] in [task_prev];
             * In this case [ls] may already be declared in [task_prev'],
             * but I don't know an easy way to check it.
             * Instead, just try to declare [ls].
             * If the attempt fails, return [task_prev']. *)
            let decl = Why3.Decl.create_param_decl ls in
            begin
              try Why3.Task.add_decl task_prev' decl
              (* [ls] is already declared, so we don't have to add it. *)
              with Why3.Decl.RedeclaredIdent _ -> task_prev'
            end
     | _ ->
        let task_prev' = apply_eqn_info task_prev eqn_info in
        if Why3.Task.task_equal task_prev task_prev' then
          task
        else
          Why3.Task.add_tdecl task_prev' tdecl

(* let apply_eqn_info task eqn_info =
 *   let task' = apply_eqn_info task eqn_info in
 *   if not (Why3.Task.task_equal task task') then
 *     debug "rewriting using %a@.%a@."
 *           Why3.Pretty.print_pr eqn_info.ei_ps Why3.Pretty.print_task task';
 *   task' *)

let apply_eqn_info_simp tasks eqn_info =
  List.map (fun task ->
            apply_eqn_info task eqn_info
            |> Why3.Trans.apply_transform "simplify_trivial_quantification"
                                          Why3api.env)
           tasks
  |> List.concat

let rewrite_using_simple_premises task =
  collect_eqns task
  |> List.filter_map
       (fun e -> match e with
                 | { ei_eqn = SimpleEqn _ } -> Some e
                 | _ -> None)
  |> List.fold_left apply_eqn_info_simp [task]
  (* |> Why3.Trans.apply_transform "simplify_trivial_quantification"
   *                               Why3api.env *)
  |> List.map (task_map_decl simplify_guards)

let rewrite_using_premises task =
  collect_eqns task
  |> List.fold_left apply_eqn_info_simp [task]
  (* |> Why3.Trans.apply_transform "simplify_trivial_quantification"
   *                               Why3api.env *)
  |> List.map (task_map_decl simplify_guards)
  (* |> (fun x ->
   *     List.iter (fun t ->
   *                debug "rewrite_using_premises returns:@.  %a@."
   *                      Why3.Pretty.print_term (Why3.Task.task_goal_fmla t)) x;
   *     x) *)


(** ---------------- quantifier elimination *)
let rec is_qf t =
  match t.t_node with
  | Tquant (_, _) -> false
  | _ -> t_all is_qf t

type literal =
  | Lit_le : polynomial -> literal
  | Lit_ge : polynomial -> literal
  | Lit_eq : polynomial -> literal
  | Lit_const : term -> literal

let lit_not = function
  | Lit_le p -> [[Lit_ge (p_add p (p_int 1))]]
  | Lit_ge p -> [[Lit_le (p_sub p (p_int 1))]]
  | Lit_eq p -> [[Lit_ge (p_add p (p_int 1))];
                 [Lit_le (p_sub p (p_int 1))]]
  | Lit_const t -> [[Lit_const (t_not_simp t)]]

let clause_not c =
  (* not (L1 and ... and Ln) <=> (not L1) or ... or (not Ln)  *)
  List.concat @@ List.map lit_not c

let lit_equal x y = match x, y with
  | Lit_le p, Lit_le q
  | Lit_ge p, Lit_ge q
  | Lit_eq p, Lit_eq q -> p_equal p q
  | Lit_const t, Lit_const t' -> t_equal t t'
  | _, _ -> false

let clause_and c1 c2 =
  let c = List.unique ~cmp:lit_equal @@ c1 @ c2 in
  (* put multiple [Lit_const]'s into one *)
  let rec f const cmps = function
    | [] -> if t_equal const t_false then
              [Lit_const t_false]
            else if t_equal const t_true then
              cmps
            else
              Lit_const const :: cmps
    | Lit_const t :: c' -> f (t_and_simp const t) cmps c'
    | l :: c' -> f const (l :: cmps) c'
  in
  f t_true [] c

let is_subset_of c c' =
   List.for_all (fun l -> List.exists (lit_equal l) c') c

let has_subset_of f c =
  List.exists (fun c' -> is_subset_of c' c) f

let rec dnf_or f1 f2 =
  match f1 with
  | [] -> f2
  | c::f1' ->
     if has_subset_of f2 c then dnf_or f1' f2 else c :: dnf_or f1' f2

let rec dnf_and f1 f2 =
  match f1 with
  | [] -> []
  | c::f1' ->
     (* (C1 or C2 or ... or Cn) and f2
      * <=> (C1 and f2) or (C2 and f2) or ... or (Cn and f2);
      * C and (C1 or ... or Cn)
      * <=> (C and C1) or (C and C2) or ... or (C and Cn);
      * C and C1 <=> union of C and C1 (considered as a clause) *)
     dnf_or (List.map (clause_and c) f2) (dnf_and f1' f2)

let rec dnf_not = function
  | [] -> [[]]                  (* not false <=> true *)
  | c::cs ->
     (* not (C1 or C2 or ... or Cn)
      * <=> not C1 and not (C2 or ... or Cn) *)
     dnf_and (clause_not c) (dnf_not cs)

let dnf_implies f1 f2 = dnf_or (dnf_not f1) f2

let dnf_iff f1 f2 = dnf_and (dnf_implies f1 f2) (dnf_implies f2 f1)

let dnf_op op f1 f2 = match op with
  | Tand -> dnf_and f1 f2
  | Tor -> dnf_or f1 f2
  | Timplies -> dnf_implies f1 f2
  | Tiff -> dnf_iff f1 f2

let nnf_of t =
  let rec nnf_pos t =
    match t.t_node with
    | Tbinop (op, t1, t2) ->
       begin
         match op with
         | Tand -> t_and_simp (nnf_pos t1) (nnf_pos t2)
         | Tor -> t_or_simp (nnf_pos t1) (nnf_pos t2)
         | Timplies -> t_or_simp (nnf_neg t1) (nnf_pos t2)
         | Tiff -> t_and_simp
                     (t_or_simp (nnf_neg t1) (nnf_pos t2))
                     (t_or_simp (nnf_neg t2) (nnf_pos t1))
       end
    | Tnot t -> nnf_neg t
    | _ -> t
  and nnf_neg t =
    match t.t_node with
    | Tbinop (op, t1, t2) ->
       begin
         match op with
         | Tand -> t_or_simp (nnf_neg t1) (nnf_neg t2)
         | Tor -> t_and_simp (nnf_neg t1) (nnf_neg t2)
         | Timplies -> t_and_simp (nnf_pos t1) (nnf_neg t2)
         | Tiff -> t_or_simp
                     (t_and_simp (nnf_pos t1) (nnf_neg t2))
                     (t_and_simp (nnf_pos t2) (nnf_neg t1))
       end
    | Tnot t -> nnf_pos t
    | _ -> t_not_simp t
  in nnf_pos t


let rec dnf_of vs t: literal list list option =
  let rec dnf t =
    (* [t]: term, [vs]: variable *)
    match t.t_node with
    | _ when not (t_v_any (vs_equal vs) t) -> Some [[Lit_const t]]
    | Tapp (ls, [t1; t2]) when is_cmp_op ps_equ && is_int t1 ->
       let p = p_sub (to_polynomial t1) (to_polynomial t2) in
       if p_contains (t_var vs) p then
         begin
           match isolate_var (t_var vs) p with
           | None -> None
           | Some (p, _) when t_v_any (vs_equal vs) (from_polynomial p) -> None
           | Some (p, s) ->
              (* debug "term %a@." Why3.Pretty.print_term t;
               * debug "%a@." Why3.Pretty.print_term
               *       (from_polynomial (p_sub (to_polynomial t1) (to_polynomial t2)));
               * debug "%a does not occur in %a@."
               *       Why3.Pretty.print_vs vs Why3.Pretty.print_term (from_polynomial p); *)
              (* t1 - t2 = s * v + p *)
              if ls_equal ls ps_equ then
                (* v = -s * p *)
                Some [[Lit_eq (if s = 1 then (p_neg p) else p)]]
              else if ls_equal ls ps_lt then
                (* v < -p if s = 1, and v > p if s = -1
                 * i.e. v <= -(p + 1) if s = 1, and v >= p + 1 if s = -1 *)
                if s = 1 then Some [[Lit_le (p_neg (p_add p (p_int 1)))]]
                else Some [[Lit_ge (p_add p (p_int 1))]]
              else if ls_equal ls ps_le then
                (* v <= -p if s = 1, and v >= p if s = -1 *)
                if s = 1 then Some [[Lit_le (p_neg p)]]
                else Some [[Lit_ge p]]
              else if ls_equal ls ps_gt then
                (* v > -p if s = 1, and v < p if s = -1 *)
                if s = 1 then Some [[Lit_ge (p_add (p_neg p) (p_int 1))]]
                else Some [[Lit_le (p_sub p (p_int 1))]]
              else            (* assert (ls_equal ls ps_ge); *)
                (* v >= -p if s = 1, and v <= p if s = -1 *)
                if s = 1 then Some [[Lit_ge (p_neg p)]]
                else Some [[Lit_le p]]
         end
       else
         (* Some (t_app ls [from_polynomial p; t_zero] None) *)
         (* In this case [vs] is not contained in [t], so this case
          * is trivial.   *)
         if t_v_any (vs_equal vs) (from_polynomial p) then
           None
         else
           begin
             match (from_polynomial p).t_node with
             | Tconst (Why3.Number.ConstInt n) ->
                let cmp =
                  if ls_equal ls ps_equ then I.eq
                  else if ls_equal ls ps_lt then I.lt
                  else if ls_equal ls ps_le then I.le
                  else if ls_equal ls ps_gt then I.gt
                  else I.ge
                in
                if cmp (Why3.Number.compute_int n) I.zero then
                  Some [[Lit_const t_true]]
                else Some [[Lit_const t_false]]
             | _ ->
                Some [[Lit_const (t_app ls [from_polynomial p; t_zero] None)]]
           end
    | Tbinop (op, t1, t2) ->
       begin
         match dnf t1, dnf t2 with
         | Some f1, Some f2 -> Some (dnf_op op f1 f2)
         | _, _ -> None
       end
    | Tnot t1 ->
       begin
         match dnf t1 with
         | Some f -> Some (dnf_not f)
         | None -> None
       end
    | _ -> None
  in dnf (nnf_of t)

(* let dnf_of vs t: literal list list option =
 *   let x = dnf_of vs t in
 *   debug "dnf_of %a...@." Why3.Pretty.print_term t;
 *   (match x with Some _ -> debug "success@." | None -> debug "fail@.");
 *   x *)

let print_literal fmt = function
  | Lit_le p -> Format.fprintf fmt "Lit_le (%a)"
                               Why3.Pretty.print_term (from_polynomial p)
  | Lit_ge p -> Format.fprintf fmt "Lit_ge (%a)"
                               Why3.Pretty.print_term (from_polynomial p)
  | Lit_eq p -> Format.fprintf fmt "Lit_eq (%a)"
                               Why3.Pretty.print_term (from_polynomial p)
  | Lit_const c -> Format.fprintf fmt "Lit_const (%a)"
                                  Why3.Pretty.print_term c

let print_dnf fmt f =
  Format.fprintf fmt "[@[";
  List.iter (fun c -> Format.fprintf fmt "[@[";
                      List.iter (Format.fprintf fmt "%a;@." print_literal) c;
                      Format.fprintf fmt "@]];@.")
            f;
  Format.fprintf fmt "@]]@."

let eliminate_quantifier_from_conj c =
  (* List.iter print_literal c; *)
  let rec collect ubs lbs eqs consts = function
    | [] -> ubs, lbs, eqs, consts
    | Lit_le t :: c' -> collect (t :: ubs) lbs eqs consts c'
    | Lit_ge t :: c' -> collect ubs (t :: lbs) eqs consts c'
    | Lit_eq t :: c' -> collect ubs lbs (t :: eqs) consts c'
    | Lit_const t :: c' -> collect ubs lbs eqs (t :: consts) c'
  in
  let p_ubs, p_lbs, p_eqs, consts = collect [] [] [] [] c in
  let ubs = List.map from_polynomial p_ubs in
  let lbs = List.map from_polynomial p_lbs in
  let eqs = List.map from_polynomial p_eqs in
  match eqs with
  | [] ->
     remove_trivial_comparison @@
       t_and_simp
         (t_and_simp_l @@
            List.concat @@
              List.map (fun l -> List.map (t_le l) ubs) lbs)
         (t_and_simp_l consts)
  | r :: rs ->
     remove_trivial_comparison @@
       t_and_simp_l @@
         t_and_simp_l (List.map (t_equ_simp r) rs) ::
           t_and_simp_l (List.map (t_le r) ubs) ::
             t_and_simp_l (List.map (t_ge r) lbs) ::
               consts

let eliminate_quantifier_from_dnf f =
  List.map (fun c -> eliminate_quantifier_from_conj c) f

(* let dnf_of vs t =
 *   debug "building dnf of %a@." Why3.Pretty.print_term t;
 *   dnf_of vs t
 *   |> (fun x -> debug "done@."; x) *)


let eliminate_linear_quantifier_1 q vs t =
  match q with
  | Tforall ->
     begin
       match dnf_of vs (t_not_simp t) with
       | Some f ->
          let ts = eliminate_quantifier_from_dnf f in
          Some (t_not_simp (t_or_simp_l ts))
       | None ->
          None
     end
  | Texists ->
     match dnf_of vs t with
     | Some f ->
        let ts = eliminate_quantifier_from_dnf f in
        Some (t_or_simp_l ts)
     | None -> None

let rec eliminate_linear_quantifier_t t =
  (* Eliminate inner quantifiers first. *)
  let t = TermTF.t_map_simp (fun t -> t) eliminate_linear_quantifier_t @@
            eliminate_unique_quant t
  in
  match t.t_node with
  | Tquant (q, tq) ->
     (* debug "eliminate_linear_quantifier_t: @[%a@]@." Why3.Pretty.print_term t; *)
     let vss, tr, t' = t_open_quant tq in
     let rec elim vss t =
       (* Tries to eliminate variables in [vss], and returns a pair
        * [vss_left, t'] where [vss_left] is the list of variables
        * that are not eliminated, and [t'] is the resulting formula. *)
       match vss with
       | [] -> [], t
       | vs::vss' ->
          let (vss_left, t') = elim vss' t in
          match eliminate_linear_quantifier_1 q vs t' with
          | Some t'' -> vss_left, t''
          | None -> vs::vss_left, t'
     in
     let vss_left, t'' = elim vss t' in
     t_quant_close_simp q vss_left tr t''
  | _ -> t

let eliminate_linear_quantifier task =
  task_map_decl
    (fun t ->
     (* debug "eliminate_linear_quantifier: @[%a@]@." Why3.Pretty.print_term t; *)
     let t' = eliminate_unique_quant t
              |> eliminate_linear_quantifier_t
              |> simplify_formula
     in
     if not (t_equal t t') then
       debug "eliminate_linear_quantifier rewrites@.  %a@.into@.  %a@."
             Why3.Pretty.print_term t Why3.Pretty.print_term t';
     t')
    task


(** ---------------- replace anonymous functions with a variable *)
let rec bind_epsilon_by_let t =
  let rec collect bvs m t =
    match t.t_node with
    | Tlet (t', tb) ->
       let m' = collect bvs m t' in
       let (vs, t'') = t_open_bound tb in
       collect (Svs.add vs bvs) m' t''
    | Tcase _ -> not_implemented "bind_epsilon_by_let, case"
    | Teps _ when Svs.for_all (fun vs -> t_v_occurs vs t = 0) bvs ->
       if Mterm.mem t m then
         Mterm.add t (Mterm.find t m + 1) m
       else
         Mterm.add t 1 m
    | Tquant (_, tq) ->
       let (vss, _, t') = t_open_quant tq in
       collect (List.fold_right Svs.add vss bvs) m t'
    | _ ->
       t_fold (collect bvs) m t
  in
  let t' = TermTF.t_map_simp (fun t -> t) bind_epsilon_by_let t in
  let m = collect Svs.empty Mterm.empty t' in
  Mterm.fold
    (fun te n t ->
     if n > 1 then
       match te.t_ty with
       | Some ty ->
          let vs = create_vsymbol (Why3.Ident.id_fresh "func") ty in
          t_let_close vs te (t_replace_simp te (t_var vs) t')
       | None -> t'
     else t')
    m t'


(** ---------------- congruence *)
let apply_congruence t =
  let modified = ref false in
  let rec apply sign t =
    match t.t_node with
    | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
       begin
         match t1.t_node, t2.t_node with
         | Tapp (ls, ts), Tapp (ls', ts')
              when ls_equal ls ls' &&
                     List.for_all2 (fun t t' ->
                                    match t.t_ty, t'.t_ty with
                                    | None, None -> true
                                    | Some ty, Some ty' -> Why3.Ty.ty_equal ty ty'
                                    | _ -> false)
                                   ts ts'
           ->
            debug "congruence matching %a@." Why3.Pretty.print_term t;
            t_and_simp_l @@ List.map2 t_equ_simp ts ts'
            |> fun t ->
               debug "returning %a@." Why3.Pretty.print_term t;
               modified := true;
               t
         | _, _ -> t
       end
    | _ -> TermTF.t_map_sign (fun _ t -> t) apply sign t
  in
  let result = apply true t in
  if !modified then Some result else None


(** ---------------- replace equality with [False] *)
(* perhaps this doesn't help much *)
let replace_equality_with_false t =
  let rec replace sign t =
    match t.t_node with
    | Tapp (ls, [{t_node = Tapp (ls', ts)}; _])
         when ls_equal ls ps_equ && ls_equal ls' fs_get ->
       (* Replace occurrences of [get _ _ = _] at positive positions
        * with [False].   *)
       if sign then t_false else t_true
    | Tbinop (Tand | Tor as op, t1, t2) ->
       t_binary_simp op (replace sign t1) (replace sign t2)
    | Tbinop (Timplies, t1, t2) ->
       t_implies_simp (replace (not sign) t1) (replace sign t2)
    | Tnot t' -> t_not_simp (replace (not sign) t')
    | _ -> TermTF.t_map_simp (fun t -> t) (replace sign) t
  in replace true t
     |> fun t' ->
        debug "replace %a@. into %a@."
              Why3.Pretty.print_term t Why3.Pretty.print_term t';
        t'


(** ---------------- eliminate ls *)
let rec eliminate_ls_t sign ls t =
  (* Replace any occurrence of an atomic formula containing [ls]
   * with true (if [sign] is true) or false (if [sign] is false). *)
  match t.t_node with
  | Tapp (_, _) ->
     if t_ls_occurs ls t then
       if sign then t_false else t_true
     else t
  | Tbinop ((Tand | Tor as op), t1, t2) ->
     t_binary_simp op (eliminate_ls_t sign ls t1)
                   (eliminate_ls_t sign ls t2)
  | Tbinop (Timplies, t1, t2) ->
     t_implies_simp (eliminate_ls_t (not sign) ls t1)
                    (eliminate_ls_t sign ls t2)
  | Tbinop (Tiff, t1, t2) ->
     t_and_simp
       (t_implies_simp (eliminate_ls_t (not sign) ls t1)
                       (eliminate_ls_t sign ls t2))
       (t_implies_simp (eliminate_ls_t (not sign) ls t2)
                       (eliminate_ls_t sign ls t1))
  | Tnot t' ->
     t_not_simp (eliminate_ls_t (not sign) ls t')
  | _ -> TermTF.t_map_simp (fun t -> t) (eliminate_ls_t sign ls) t

let eliminate_ls ls task =
  let rec elim tdecls task =
    match task with
    | None -> tdecls, task
    | Some {
          Why3.Task.task_decl = tdecl;
          Why3.Task.task_prev = task_prev;
        } ->
       match tdecl.Why3.Theory.td_node with
       | Why3.Theory.Decl {
           Why3.Decl.d_node = Why3.Decl.Dparam ls'
         } when ls_equal ls' ls ->
          (* Nothing more to be eliminated. *)
          tdecls, task_prev
       | Why3.Theory.Decl {
             Why3.Decl.d_node = Why3.Decl.Dprop (k, pr, t)
           } ->
          let t' = eliminate_ls_t (k = Why3.Decl.Pgoal) ls t in
          if t_equal t' t_true && k <> Why3.Decl.Pgoal then
            elim (tdecl :: tdecls) task_prev
          else
            elim ((Why3.Theory.create_decl @@
                     Why3.Decl.create_prop_decl k pr t') :: tdecls)
                 task_prev
       | _ ->
          elim (tdecl :: tdecls) task_prev
  in
  let tdecls, task = elim [] task
  in List.fold_left Why3.Task.add_tdecl task tdecls

(** ---------------- simplify affine (in)equalities *)
let collect_ls_bounds task =
  let decls = Why3.Task.task_decls task in
  let rec collect decls acc =
    match decls with
    | decl :: decls' ->
       let acc' =
         match decl.Why3.Decl.d_node with
         | Why3.Decl.Dparam ({ ls_args = []; ls_value = Some ty } as ls)
              when Why3.Ty.ty_equal ty ty_int ->
            if List.exists (function
                             | { Why3.Decl.d_node =
                                   Why3.Decl.Dprop (Why3.Decl.Paxiom, _, ax) } ->
                                check_lower_bound Texists (t_ls ls) ax
                             | _ -> false)
                           decls'
            then
              List.map (function
                         | { Why3.Decl.d_node =
                               Why3.Decl.Dprop (Why3.Decl.Paxiom, _, ax) } ->
                            find_upper_bounds Texists (t_ls ls) ax
                         | _ -> Sterm.empty)
                       decls'
              |> List.fold_left Sterm.union Sterm.empty
              |> (fun ts -> Mterm.add (t_ls ls) ts acc)
            else acc
         | _ -> acc
       in collect decls' acc'
    | [] -> acc
  in collect decls Mterm.empty

let why3_bigInt_gcd n1 n2 =
  let rec euclid x y =
    (* assume x >= y *)
    if I.eq I.zero y then x
    else euclid y (I.euclidean_mod x y)
  in
  let x = I.abs n1 in
  let y = I.abs n2 in
  if I.ge x y then euclid x y else euclid y x

let term_list_intersect ts1 ts2 =
  List.filter (fun t -> List.exists (t_equal t) ts1) ts2

let common_factor p =
  let ts, ns = List.split (PTerm.p_repr p) in
  let m =
    match ts with
    | t :: ts' -> List.fold_left term_list_intersect t ts'
    | [] -> []
  in
  let n =
    match ns with
    | n :: ns' -> List.fold_left why3_bigInt_gcd n ns'
    | [] -> I.zero
  in
  m, n

let from_polynomial_opt = function
  | Some p -> from_polynomial p
  | None -> implementation_error "from_polynomial_opt"

let rec find_first list f = match list with
  | x :: xs ->
     begin match f x with None -> find_first xs f | r -> r end
  | [] -> None

let simp_op bounds cmp t1 t2 : term option =
  (* in case t1 and t2 have a common factor;
   * but we consider only common monomials *)
  let p1 = to_polynomial t1 in
  let p2 = to_polynomial t2 in
  (* transpose terms with negative coefficients *)
  let p1, p2 =
    let p = p_repr @@ p_sub p1 p2 in
    let pos, neg = List.partition (fun (_, n) -> I.gt n I.zero) p in
    of_repr pos, p_neg (of_repr neg)
  in
  let m1, n1 = common_factor p1 in
  let m2, n2 = common_factor p2 in
  let m = if I.eq I.zero n1 then m2
          else if I.eq I.zero n2 then m1
          else term_list_intersect m1 m2
  in
  let n = why3_bigInt_gcd n1 n2 in
  if I.eq n I.zero then
    begin
      (* t1 = t2 = 0 *)
      assert (p_repr p1 = []);
      assert (p_repr p2 = []);
      match cmp with
      | `Le | `Eq | `Ge -> Some t_true
      | _ -> Some t_false
    end
  else if m = [] && I.eq n I.one then
    (* no common factor *)
    let repr1 = p_repr p1 in
    let repr2 = p_repr p2 in
    let is_var = function
      | [{ t_node = Tvar _ } as v], n
      | [{ t_node = Tapp(_, []) } as v], n ->
         if I.eq n I.one
         then Some (v, 1)
         else if I.eq n (I.minus I.one)
         then Some (v, -1)
         else None
      | _ -> None
    in
    let vs1 = List.filter_map is_var repr1 in
    let vs2 = List.filter_map is_var repr2 in
    if vs1 <> [] && vs2 <> [] then
      let _ =
        debug "t1 = %a, and@." Why3.Pretty.print_term t1;
        debug "t2 = %a@." Why3.Pretty.print_term t2;
      in
      let mk_cmp s v1 v2 q1 q2 =
        (* here pi = s * vi + b * qi;
         * note: we may assume 0 <= vi < b *)
        match cmp with
        | `Lt ->
           (* s * v1 + b * q1 < s * v2 + b * q2
            *  <=> q1 < q2 \/ (q1 = q2 /\ s * v1 < s * v2) *)
           t_or (t_lt q1 q2)
                (t_and (t_equ q1 q2)
                       (if s = 1 then t_lt v1 v2
                        else t_lt v2 v1))
        | `Le ->
           (* s * v1 + b * q1 <= s * v2 + b * q2
            *  <=> q1 < q2 \/ (q1 = q2 /\ s * v1 <= s * v2) *)
           t_or (t_lt q1 q2)
                (t_and (t_equ q1 q2)
                       (if s = 1 then t_le v1 v2
                        else t_le v2 v1))
        | `Eq ->
           (* s * v1 + b * q1 = s * v2 + b * q2
            *  <=> q1 = q2 /\ v1 = v2 *)
           t_and (t_equ q1 q2) (t_equ v1 v2)
        | `Gt ->
           (* s * v1 + b * q1 > s * v2 + b * q2
            *  <=> q1 > q2 \/ (q1 = q2 /\ s * v1 > s * v2) *)
           t_or (t_lt q2 q1)
                (t_and (t_equ q1 q2)
                       (if s = 1 then t_lt v2 v1
                        else t_lt v1 v2))
        | `Ge ->
           (* s * v1 + b * q1 >= s * v2 + b * q2
            *  <=> q1 > q2 \/ (q1 = q2 /\ s * v1 >= s * v2) *)
           t_or (t_lt q2 q1)
                (t_and (t_equ q1 q2)
                       (if s = 1 then t_le v2 v1
                        else t_le v1 v2))
      in
      let do_simp s v1 v2 b =
        (* p1 = s * v1 + p1', p2 = s * v2 + p2' *)
        let p1' = p_sub p1 (p_mult (p_int s) (p_var v1)) in
        let p2' = p_sub p2 (p_mult (p_int s) (p_var v2)) in
        match p_divide p1' b, p_divide p2' b with
        | None, _ | _, None -> None
        | Some q1', Some q2' ->
           (* p1 = s * v1 + b * q1, p2 = s * v2 + b * q2 *)
           let q1 = from_polynomial q1' in
           let q2 = from_polynomial q2' in
           Some (mk_cmp s v1 v2 q1 q2 |> remove_trivial_comparison)
      in
      find_first vs1 @@
        (fun (v1, s1) ->
         (* debug "v1 = %a; s1 = %a@." Why3.Pretty.print_term v1
          *       Format.pp_print_int s1; *)
         find_first vs2 @@
           (fun (v2, s2) ->
            (* debug "v2 = %a; s2 = %a@." Why3.Pretty.print_term v2
             *       Format.pp_print_int s2; *)
            if s1 = s2 then
              find_first (Mterm.find_def [] v2 bounds)
                         (fun b ->
                          if List.exists (p_equal b)
                                         (Mterm.find_def [] v1 bounds)
                          then (do_simp s1 v1 v2 b)
                          else None)
            else None))
    else if vs1 = [] && vs2 = [] then
      None
    else
      (* exactly one of p1 or p2 has the form s * v + q;
       * by swapping p1 and p2 if necessary, we may assume
       * p1 = s * v + b * q1, p2 = b * q2, and 0 <= v < b *)
      let vs, p1, p2, cmp =
        if vs1 <> [] then (vs1, p1, p2, cmp)
        else (vs2, p2, p1,
              match cmp with
                `Le -> `Ge | `Lt -> `Gt | `Eq -> `Eq | `Ge -> `Le | `Gt -> `Lt)
      in
      let mk_cmp s v q1 q2 =
        (* p1 = s * v + b * q1; p2 = b * q2 *)
        match cmp with
        | `Lt ->
           (* s * v + b * q1 < b * q2
            *  <=> q1 < q2 \/ (q1 = q2 /\ s * v < 0)
            *  <=> if s = 1 then q1 < q2
            *      else q1 < q2 \/ (q1 = q2 /\ 0 < v) *)
           if s = 1 then t_lt q1 q2
           else
             t_or (t_lt q1 q2)
                  (t_and (t_equ q1 q2) (t_lt t_zero v))
        | `Le ->
           (* s * v + b * q1 <= b * q2
            *  <=> q1 < q2 \/ (q1 = q2 /\ s * v <= 0)
            *  <=> if s = 1 then q1 < q2 \/ (q1 = q2 /\ v = 0)
            *      else q1 < q2 \/ q1 = q2 *)
           t_or (t_lt q1 q2)
                (if s = 1 then t_and (t_equ q1 q2) (t_equ v t_zero)
                 else t_equ q1 q2)
        | `Eq ->
           (* s * v + b * q1 = b * q2
            *  <=> q1 = q2 /\ v = 0 *)
           t_and (t_equ q1 q2) (t_equ v t_zero)
        | `Gt ->
           (* s * v + b * q1 > b * q2
            *  <=> q1 > q2 \/ (q1 = q2 /\ s * v > 0)
            *  <=> if s = 1 then q1 > q2 \/ (q1 = q2 /\ 0 < v)
            *      else q1 > q2  *)
           if s = 1 then
             t_or (t_gt q1 q2)
                  (t_and (t_equ q1 q2) (t_lt t_zero v))
           else t_gt q1 q2
        | `Ge ->
           (* s * v + b * q1 >= b * q2
            *  <=> q1 > q2 \/ (q1 = q2 /\ s * v >= 0)
            *  <=> if s = 1 then q1 > q2 \/ q1 = q2
            *      else q1 > q2 \/ (q1 = q2 /\ v = 0) *)
           t_or (t_gt q1 q2)
                (if s = 1 then t_equ q1 q2
                 else t_and (t_equ q1 q2) (t_equ v t_zero))
      in
      let do_simp1 b s v =
        let p1' = p_sub p1 (p_mult (p_int s) (p_var v)) in
        match p_divide p1' b, p_divide p2 b with
        | None, _ | _, None -> None
        | Some q1', Some q2' ->
           let q1 = from_polynomial q1' in
           let q2 = from_polynomial q2' in
           debug "t1 = %a@." Why3.Pretty.print_term t1;
           debug "t2 = %a@." Why3.Pretty.print_term t2;
           debug "s, v = %a, %a@." Format.pp_print_int s Why3.Pretty.print_term v;
           debug "b = %a@." Why3.Pretty.print_term (from_polynomial b);
           debug "p1 = %a@." Why3.Pretty.print_term @@ from_polynomial p1;
           debug "p1' = %a@." Why3.Pretty.print_term @@ from_polynomial p1';
           debug "p2 = %a@." Why3.Pretty.print_term @@ from_polynomial p2;
           debug "q1 = %a@." Why3.Pretty.print_term q1;
           debug "q2 = %a@." Why3.Pretty.print_term q2;
           Some (mk_cmp s v q1 q2)
      in
      find_first vs
                 (fun (v, s) ->
                  find_first (Mterm.find_def [] v bounds)
                             (fun b -> do_simp1 b s v))
  else
    (* found a common factor *)
    let factor = List.fold_left p_mult (p_bigint n) @@ List.map p_var m in
    (* debug "found common factor: %a@." Why3.Pretty.print_term (from_polynomial factor); *)
    assert (I.gt n I.zero);
    let q1 = match p_divide p1 factor with
      | Some q -> from_polynomial q
      | None -> implementation_error "in simplify_affine_formula"
    in
    let q2 = match p_divide p2 factor with
      | Some q -> from_polynomial q
      | None -> implementation_error "in simplify_affine_formula"
    in
    if m = [] then
      (* factor is a (positive) constant; remove it *)
      match cmp with
      | `Lt -> Some (t_lt q1 q2)
      | `Le -> Some (t_le q1 q2)
      | `Eq -> Some (t_equ q1 q2)
      | `Gt -> Some (t_gt q1 q2)
      | `Ge -> Some (t_ge q1 q2)
    else if (t_equal q1 t_one || t_equal q1 t_zero) &&
              (t_equal q2 t_one || t_equal q2 t_zero)
    then
      (* factor is not a constant, but the quotient is trivial *)
      None
    else
      let d = from_polynomial factor in
      (* t1 = q1 * d <cmp> t2 = q2 * d *)
      let result =
        match cmp with
        | `Le ->
           (* q1 * d <= q2 * d <=> (q1 <= q2 /\ d >= 0) \/ (q1 >= q2 /\ d <= 0) *)
           t_or (t_and (t_le q1 q2) (t_le t_zero d))
                (t_and (t_le q2 q1) (t_le d t_zero))
        | `Lt -> 
           (* q1 * d < q2 * d <=> (q1 < q2 /\ d > 0) \/ (q1 > q2 /\ d < 0) *)
           t_or (t_and (t_lt q1 q2) (t_lt t_zero d))
                (t_and (t_lt q2 q1) (t_lt d t_zero))
        | `Eq -> 
           (* q1 * d = q2 * d <=> (q1 = q2 \/ d = 0) *)
           t_or (t_equ q1 q2) (t_equ t_zero d)
        | `Ge -> 
           (* q1 * d >= q2 * d <=> (q1 >= q2 /\ d >= 0) \/ (q1 <= q2 /\ d <= 0) *)
           t_or (t_and (t_le q2 q1) (t_le t_zero d))
                (t_and (t_le q1 q2) (t_le d t_zero))
        | `Gt -> 
           (* q1 * d > q2 * d <=> (q1 > q2 /\ d > 0) \/ (q1 < q2 /\ d < 0) *)
           t_or (t_and (t_lt q2 q1) (t_lt t_zero d))
                (t_and (t_lt q1 q2) (t_lt d t_zero))
      in Some (remove_trivial_comparison result)

let simplify_affine_formula task =
  let filter_ub t =
    (* returns [Some p] if t consists of a single term,
     * where [p] is a polynomial corresponding to t *)
    let p = to_polynomial t in
    match p_repr p with
    | [] | [_] -> Some p
    | _ -> None
  in
  let bounds = Mterm.map (fun ubs ->
                          List.filter_map filter_ub @@ Sterm.elements ubs)
               @@ collect_ls_bounds task
  in
  let is_atomic t = match t.t_node with
    | Tvar _
    | Tapp (_, [])
    | Tconst _ -> true
    | _ -> false
  in
  let rec simp bounds t =
    match t.t_node with
    | Tapp (ls, [t1; t2]) when is_int t1 ->
       if is_atomic t1 && is_atomic t2 then t
       else
         let repeat = function
           | Some t'  ->
              if t_equal t t' then t
              else
                (debug "simp %a@." Why3.Pretty.print_term t;
                 debug "==> %a@." Why3.Pretty.print_term t';
                 simp bounds @@ remove_trivial_comparison t')
           | None -> t
         in
         if ls_equal ls ps_le then simp_op bounds `Le t1 t2 |> repeat
         else if ls_equal ls ps_lt then
           match simp_op bounds `Lt t1 t2 with
           | Some _ as r -> repeat r
           | None -> simp_op bounds `Le t1 (t_minus t2 t_one) |> repeat
         else if ls_equal ls ps_equ then simp_op bounds `Eq t1 t2 |> repeat
         else if ls_equal ls ps_ge then simp_op bounds `Ge t1 t2 |> repeat
         else if ls_equal ls ps_gt then simp_op bounds `Gt t1 t2 |> repeat
         else t
    | Tquant (q, tq) ->
       (* Problem: if i < N is added to a bound list,
        * the procedure tries to remove i < N itself.
        * As a workaround, we separate guards and body. *)
       let (vss, triggers, body) = t_open_quant tq in
       let bounds' =
         List.fold_left (fun bounds vs ->
                         let v = t_var vs in
                         if is_int v && check_lower_bound q v body then
                           let ubs = Sterm.elements @@
                                       find_upper_bounds q v body
                                     |> List.filter_map
                                          (fun ub ->
                                           if t_v_occurs vs ub = 0 then
                                             filter_ub ub
                                           else None)
                           in
                           if ubs = [] then bounds
                           else Mterm.add v ubs bounds
                         else bounds)
                        bounds (List.rev vss)
       in
       let body' = simp bounds' body in
       let guard =
         List.map (fun vs ->
                   let ubs = Mterm.find_def [] (t_var vs) bounds' in
                   t_le t_zero (t_var vs) ::
                     List.map (fun ub -> t_lt (t_var vs) @@ from_polynomial ub) ubs)
                  vss
         |> List.concat
         |> t_and_simp_l
       in
       let body'' = match q with
         | Tforall -> t_implies_simp guard body'
         | Texists -> t_and_simp guard body'
       in
       t_quant_close_simp q vss triggers @@ simplify_guards body''
    | _ ->
       TermTF.t_map_simp (fun x -> x) (simp bounds) t
  in
  Why3util.transform_goal (simp bounds) task

(** ----------------unmerge quantifiers *)

(* let unmerge_quantifiers task =
 *   let bounds = collect_ls_bounds task in
 *   
 *   Why3util.transform_goal (simp bounds) task *)
