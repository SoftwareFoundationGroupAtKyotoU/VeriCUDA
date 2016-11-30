
type var_kind = Local | Shared | Global | Formal

val ty_of_kind : var_kind -> Why3.Ty.ty -> Why3.Ty.ty

val t_tid_of : Why3.Term.term -> Why3.Term.term
val t_bid_of : Why3.Term.term -> Why3.Term.term
val t_bdim : Why3.Term.term
val t_gdim : Why3.Term.term
val t_bdimx : Why3.Term.term
val t_bdimy : Why3.Term.term
val t_bdimz : Why3.Term.term
val t_gdimx : Why3.Term.term
val t_gdimy : Why3.Term.term
val t_gdimz : Why3.Term.term

val t_dim3 : Why3.Term.term -> Why3.Term.term -> Why3.Term.term ->
             Why3.Term.term
val t_x : Why3.Term.term -> Why3.Term.term
val t_y : Why3.Term.term -> Why3.Term.term
val t_z : Why3.Term.term -> Why3.Term.term

val t_acc_local : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val fs_bid_of : Why3.Term.lsymbol
val t_bid_of : Why3.Term.term -> Why3.Term.term
val t_acc_shared : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_acc_global : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
(* val t_array_get1 : Why3.Term.term -> Why3.Term.term -> Why3.Term.term *)
(* val t_array_get : Why3.Term.term -> Why3.Term.term list -> Why3.Term.term *)
(* val t_array_set : Why3.Term.term -> Why3.Term.term list -> Why3.Term.term -> Why3.Term.term *)
(* val fs_get : Why3.Term.lsymbol *)
(* val t_get : Why3.Term.term -> Why3.Term.term -> Why3.Term.term *)
(* val t_get1 : Why3.Term.term -> Why3.Term.term -> Why3.Term.term *)
val create_logic_var : string -> Why3.Ty.ty -> Why3.Term.vsymbol
val ps_is_valid_thread : Why3.Term.lsymbol
val ps_is_valid_tid : Why3.Term.lsymbol
val ps_is_valid_bid : Why3.Term.lsymbol
val t_is_valid_thread : Why3.Term.term -> Why3.Term.term
val t_is_valid_bid : Why3.Term.term -> Why3.Term.term
val t_is_valid_tid : Why3.Term.term -> Why3.Term.term
val t_uminus : Why3.Term.term -> Why3.Term.term
val t_real_uminus : Why3.Term.term -> Why3.Term.term

val coerce_to_real : Why3.Term.term -> Why3.Term.term
val t_arith_op :
  Why3.Term.lsymbol ->
  Why3.Term.lsymbol -> Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_plus : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_minus : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_mult : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_div : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_mod : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_pow : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_arith_rel :
  Why3.Term.lsymbol ->
  Why3.Term.lsymbol -> Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_lt : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_gt : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_le : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_ge : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_eq : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_ne : Why3.Term.term -> Why3.Term.term -> Why3.Term.term
val t_zero : Why3.Term.term

val t_forall_threads : Why3.Term.vsymbol -> Why3.Term.trigger -> Why3.Term.term -> Why3.Term.term
val t_exists_threads : Why3.Term.vsymbol -> Why3.Term.trigger -> Why3.Term.term -> Why3.Term.term

(* val extend_table : ('a * 'b) list -> 'a -> 'b -> ('a * 'b) list *)
val translate : (Why3.Term.term -> Why3.Term.term) ->
                Why3.Term.term ->
                (string * (var_kind option * Why3.Term.term)) list ->
                Ftree.parsetree ->
                Why3.Term.term
