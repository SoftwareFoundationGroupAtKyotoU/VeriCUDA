(*
#use "topfind"
#require "why3"
#require "cil"
 *)

(* open Cil *)
open Why3.Term
open Why3api

(* determine the kind (local/shared/global) of varinfo *)

type var_kind = Local | Shared | Global | Formal

let ty_of_kind k t =
  match k with
  | Local -> ty_local t
  | Shared -> ty_shared t
  | Global -> ty_global t
  | Formal -> t


let t_tid_of t = t_app fs_tid_of [t] (Some ty_dim3)
let t_bid_of t = t_app fs_bid_of [t] (Some ty_dim3)
let t_bdim = t_app fs_bdim [] (Some ty_dim3)
let t_gdim = t_app fs_gdim [] (Some ty_dim3)
let t_bdimx = t_app fs_x [t_bdim] (Some ty_int)
let t_gdimx = t_app fs_x [t_gdim] (Some ty_int)
let t_bdimy = t_app fs_y [t_bdim] (Some ty_int)
let t_gdimy = t_app fs_y [t_gdim] (Some ty_int)
let t_bdimz = t_app fs_z [t_bdim] (Some ty_int)
let t_gdimz = t_app fs_z [t_gdim] (Some ty_int)

let t_dim3 x y z = t_app fs_mk_dim3 [x; y; z] (Some ty_dim3)

let t_x t = t_app fs_x [t] (Some ty_int)
let t_y t = t_app fs_y [t] (Some ty_int)
let t_z t = t_app fs_z [t] (Some ty_int)

let ps_is_valid_thread =
  Why3.Theory.ns_find_ls cuda_export ["is_valid_thread"]

let t_is_valid_thread t =
  ps_app ps_is_valid_thread [t]

let ps_is_valid_tid =
  Why3.Theory.ns_find_ls cuda_export ["is_valid_tid"]

let t_is_valid_tid t =
  ps_app ps_is_valid_tid [t]

let ps_is_valid_bid =
  Why3.Theory.ns_find_ls cuda_export ["is_valid_bid"]

let t_is_valid_bid t =
  ps_app ps_is_valid_bid [t]

let t_forall_threads ts triggers t =
  t_forall_close_simp [ts] triggers (t_implies_simp
                                       (t_is_valid_thread (t_var ts))
                                       t)

let t_exists_threads ts triggers t =
  t_exists_close_simp [ts] triggers (t_and_simp
                                       (t_is_valid_thread (t_var ts))
                                       t)

let t_acc_local x t = t_get x t

let t_notb t =
  if t_equal t t_bool_true then t_bool_false
  else if t_equal t t_bool_false then t_bool_true
  else fs_app fs_notb [t] Why3.Ty.ty_bool

let t_andb t1 t2 =
  if t_equal t1 t_bool_true then t2
  else if t_equal t2 t_bool_true then t1
  else if t_equal t1 t_bool_false || t_equal t2 t_bool_false then t_bool_false
  else fs_app fs_andb [t1; t2] Why3.Ty.ty_bool

let fs_bid_of = Why3.Theory.ns_find_ls cuda_export ["bid_of"]

let t_bid_of t = t_app_infer fs_bid_of [t]

let t_acc_shared x t = t_get x (t_bid_of t)

let t_acc_global x _ = x

(* let t_array_get1 t i = t_app_infer fs_array_get [t; i] *)

(* let t_array_get t indices = *)
(*   List.fold_left t_array_get1 t indices *)

(* let t_array_set1 t i v = *)
(*   t_app_infer fs_array_set [t; i; v] *)

(* let rec t_array_set t indices v = match indices with *)
(*   | [] -> v                     (\* should raise an exception? *\) *)
(*   | i :: is -> *)
(*      t_array_set1 t i (t_array_set (t_array_get t [i]) is v) *)

let t_map_get t key = t_get t key

let create_logic_var name ty =
  create_vsymbol (Why3.Ident.id_fresh name) ty

let t_binary_op op lhs rhs = t_app_infer op [lhs; rhs]
let t_unary_op op arg = t_app_infer op [arg]

let t_uminus t = t_unary_op fs_uminus t
let t_real_uminus t = t_unary_op fs_real_uminus t

(* let from_int_theory = Why3.Env.read_theory env ["real"] "FromInt" *)
(* let fs_from_int = *)
(*   Why3.Theory.ns_find_ls from_int_theory.Why3.Theory.th_export ["from_int"] *)

let coerce_to_real x : term =
  match x.t_ty with
  | Some ty when Why3.Ty.ty_equal ty ty_real -> x
  | Some ty when Why3.Ty.ty_equal ty ty_int ->
     t_app fs_from_int [x] (Some ty_real)
  | _ -> failwith "cannot coerce types other than int to real"

let t_arith_op fs_r fs_i t1 t2 : term =
  match t1.t_ty, t2.t_ty with
  | Some ty1, Some ty2
       when Why3.Ty.ty_equal ty1 ty_real || Why3.Ty.ty_equal ty2 ty_real ->
     t_app fs_r [coerce_to_real t1; coerce_to_real t2] (Some ty_real)
  | Some ty1, Some ty2
       when Why3.Ty.ty_equal ty1 ty_int && Why3.Ty.ty_equal ty2 ty_int ->
     t_app fs_i [t1; t2] (Some ty_int)
  | _ -> 
     Format.printf "arithmetic operation applied to: ";
     begin match t1.t_ty with
           | None -> Format.printf "formula, "
           | Some ty -> Format.printf "@[%a@], " Why3.Pretty.print_ty ty
     end;
     begin match t2.t_ty with
           | None -> Format.printf "formula@."
           | Some ty -> Format.printf "@[%a@]@." Why3.Pretty.print_ty ty
     end;
     failwith "type error: arithmetic operations expect int/real"

let t_plus t1 t2 = t_arith_op fs_real_plus fs_plus t1 t2
let t_minus t1 t2 = t_arith_op fs_real_minus fs_minus t1 t2
let t_mult t1 t2 = t_arith_op fs_real_mult fs_mult t1 t2
let t_div t1 t2 = t_arith_op fs_real_div fs_div t1 t2
let t_mod t1 t2 =
  assert (match t1.t_ty with Some t -> Why3.Ty.ty_equal t ty_int | _ -> false);
  assert (match t2.t_ty with Some t -> Why3.Ty.ty_equal t ty_int | _ -> false);
  t_app fs_mod [t1; t2] (Some ty_int)
(* let t_asl t1 t2 = *)
(* let t_asr t1 t2 = *)
let t_pow t1 t2 = t_arith_op fs_real_pow fs_pow t1 t2

let t_arith_rel ps_r ps_i t1 t2 : term =
  match t1.t_ty, t2.t_ty with
  | Some ty1, Some ty2
       when Why3.Ty.ty_equal ty1 ty_real || Why3.Ty.ty_equal ty2 ty_real ->
     t_app ps_r [coerce_to_real t1; coerce_to_real t2] None
  | Some ty1, Some ty2
       when Why3.Ty.ty_equal ty1 ty_int && Why3.Ty.ty_equal ty2 ty_int ->
     t_app ps_i [t1; t2] None
  | _ ->
     Format.printf "arithmetic relation applied to: ";
     begin match t1.t_ty with
           | None -> Format.printf "formula, "
           | Some ty -> Format.printf "@[%a@], " Why3.Pretty.print_ty ty
     end;
     begin match t2.t_ty with
           | None -> Format.printf "formula@."
           | Some ty -> Format.printf "@[%a@]@." Why3.Pretty.print_ty ty
     end;
     failwith ("type error: arithmetic relations expect int/real")

let t_lt t1 t2 = t_arith_rel ps_real_lt ps_lt t1 t2
let t_gt t1 t2 = t_arith_rel ps_real_gt ps_gt t1 t2
let t_le t1 t2 = t_arith_rel ps_real_le ps_le t1 t2
let t_ge t1 t2 = t_arith_rel ps_real_ge ps_ge t1 t2
let t_eq t1 t2 = t_arith_rel ps_equ ps_equ t1 t2
let t_ne t1 t2 = t_neq t1 t2
(* let t_tuple ts = match ts with *)
(*   | [x] -> x *)
(*   | _ -> t_tuple ts *)
let t_zero = t_nat_const 0

let t_sum f a b =
  match f.t_ty with
  | Some { Why3.Ty.ty_node = Why3.Ty.Tyapp (ts, [ty1; ty2]) }
       when Why3.Ty.ty_equal ty1 ty_int &&
              Why3.Ty.ty_equal ty2 ty_int ->
     (* this function returns int *)
     fs_app fs_sum_i [f; a; b] ty_int
  | Some { Why3.Ty.ty_node = Why3.Ty.Tyapp (ts, [ty1; ty2]) }
       when Why3.Ty.ty_equal ty1 ty_int &&
              Why3.Ty.ty_equal ty2 ty_real ->
     (* this function returns real *)
     fs_app fs_sum_r [f; a; b] ty_real
  | _ ->
     failwith "type error: first argument of sum should be a function\
               returning either int or real"


(** parse tree -> why3 term *)

open Ftree

(*
translation from parse trees into why3 terms
during translation we use association list of the form (name, (kind, vsym))
its key, name, is a name occurring in a parse tree
kind is its memory space; None means that it is a logic variable
vsym is the vsymbol of why3 to which the name should be mapped
 *)

let extend_table tbl s k t = (s, (k, t)) :: tbl

let rec translate mask texp tbl = function
  | PTTrue -> t_true
  | PTFalse -> t_false
  | PTImpl (es, e) ->
     let lhs = t_and_simp_l (List.map (translate mask texp tbl) es) in
     t_implies_simp lhs (translate mask texp tbl e)
  | PTOr es -> t_or_simp_l (List.map (translate mask texp tbl) es)
  | PTAnd es -> t_and_simp_l (List.map (translate mask texp tbl) es)
  | PTNot e -> t_not_simp @@ translate mask texp tbl e
  | PTForall (x, ts, e) ->
     (* for the time being we fix type of x to int *)
     let vsym = create_logic_var x ty_int in
     let var = t_var vsym in
     let tbl' = extend_table tbl x None var in
     let triggers =
       if !Options.use_triggers_flag then
         List.map (fun t -> [translate mask texp tbl' t]) ts
       else []
     in
     t_forall_close [vsym] triggers (translate mask texp tbl' e)
  | PTForallThread (x, ts, e) ->
     let vsym = create_logic_var x ty_thread in
     let var = t_var vsym in
     let tbl' = extend_table tbl x None var in
     let triggers =
       if !Options.use_triggers_flag then
         List.map (fun t -> [translate mask texp tbl' t]) ts
       else []
     in
     t_forall_threads vsym triggers (translate mask var tbl' e)
  | PTExists (x, ts, e) ->
     let vsym = create_logic_var x ty_int in
     let var = t_var vsym in
     let tbl' = extend_table tbl x None var in
     let triggers =
       if !Options.use_triggers_flag then
         List.map (fun t -> [translate mask texp tbl' t]) ts
       else []
     in
     t_exists_close [vsym] triggers (translate mask texp tbl' e)
  | PTExistsThread (x, ts, e) ->
     let vsym = create_logic_var x ty_thread in
     let var = t_var vsym in
     let tbl' = extend_table tbl x None var in
     let triggers =
       if !Options.use_triggers_flag then
         List.map (fun t -> [translate mask texp tbl' t]) ts
       else []
     in
     t_exists_threads vsym triggers (translate mask var tbl' e)
  | PTEq (e1, e2) -> t_eq (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTNeq (e1, e2) -> t_ne (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTLT (e1, e2) -> t_lt (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTGT (e1, e2) -> t_gt (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTLE (e1, e2) -> t_le (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTGE (e1, e2) -> t_ge (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTPlus (e1, e2) -> t_plus (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTMinus (e1, e2) -> t_minus (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTMult (e1, e2) -> t_mult (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTDiv (e1, e2) -> t_div (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTMod (e1, e2) -> t_mod (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTPow (e1, e2) -> t_pow (translate mask texp tbl e1) (translate mask texp tbl e2)
  | PTUminus e -> t_uminus (translate mask texp tbl e)
  | PTInt n -> t_const (Why3.Number.ConstInt
                          (Why3.Number.int_const_dec @@ string_of_int n))
  | PTSum (x, e, a, b) ->
     let vs = create_vsymbol (Why3.Ident.id_fresh x) ty_int in
     let tbl' = (x, (None, t_var vs)) :: tbl in
     let fbody = translate mask texp tbl' e in
     let ty =
       match fbody.t_ty with
       | Some ty when Why3.Ty.ty_equal ty ty_int ||
                        Why3.Ty.ty_equal ty ty_real
         -> ty
       | _ ->
          failwith "function being summed should return either int or real"
     in
     let f = create_vsymbol (Why3.Ident.id_fresh "f")
                            (Why3.Ty.ty_func ty_int ty) in
     let spec = t_forall_close [vs] [] @@
                  t_equ (t_func_app (t_var f) (t_var vs)) fbody
     in
     t_sum (t_eps_close f spec)
           (translate mask texp tbl a) (translate mask texp tbl b)
  | PTAt (e, t) ->
     let t' = translate mask texp tbl t in translate mask t' tbl e
  | PTAcc (x, es) ->
     let (k, var) = try List.assoc x tbl
                    with Not_found -> failwith @@ "unbound variable: " ^ x
     in
     let indexes = t_tuple (List.map (translate mask texp tbl) es) in
     begin
       match k with
       | Some Local -> t_get (t_acc_local var texp) indexes
       | Some Shared -> t_get (t_acc_shared var texp) indexes
       | Some Global -> t_get (t_acc_global var texp) indexes
       | Some Formal -> t_get var indexes
       (* | None -> assert (es = []); var *)
       (* the above causes an assertion failure when logic param is
        * declared as an array type *)
       | None -> if es = [] then var else t_get var indexes
     end
  | PTAct x -> mask texp
  | PTConst (c, d) ->
     let accessor = match d with
       | X -> t_x
       | Y -> t_y
       | Z -> t_z
     in
     match c with
       TID -> accessor (t_tid_of texp)
     | BID -> accessor (t_bid_of texp)
     | BDIM -> accessor t_bdim (* (t_acc_global t_bdim texp) *)
     | GDIM -> accessor t_gdim (* (t_acc_global t_gdim texp) *)

