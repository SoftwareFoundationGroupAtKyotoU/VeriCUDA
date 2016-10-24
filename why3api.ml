(* Constants and functions manipulating why3 symbols and terms. *)

let config = Why3.Whyconf.read_config None
let env =
  let main = Why3.Whyconf.get_main config in
  Why3.Env.create_env (Why3.Whyconf.loadpath main)


(** integers **)
let ty_int = Why3.Ty.ty_int

let t_one = Why3.Term.t_nat_const 1

let int_theory = Why3.Env.read_theory env ["int"] "Int"
let ps_le = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["infix <="]
let ps_lt = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["infix <"]
let ps_ge = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["infix >="]
let ps_gt = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["infix >"]
let fs_plus = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["infix +"]
let fs_minus = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["infix -"]
let fs_uminus = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["prefix -"]
let fs_mult = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["infix *"]

let computerdiv_theory = Why3.Env.read_theory env ["int"] "ComputerDivision"
let fs_div = Why3.Theory.ns_find_ls computerdiv_theory.Why3.Theory.th_export ["div"]
let fs_mod = Why3.Theory.ns_find_ls computerdiv_theory.Why3.Theory.th_export ["mod"]

let power_theory = Why3.Env.read_theory env ["int"] "Power"
let fs_pow = Why3.Theory.ns_find_ls power_theory.Why3.Theory.th_export ["power"]
let fs_uminus = Why3.Theory.ns_find_ls int_theory.Why3.Theory.th_export ["prefix -"]


(** maps *)
let map_theory = Why3.Env.read_theory env ["map"] "Map"

let ts_map = Why3.Theory.ns_find_ts map_theory.Why3.Theory.th_export ["map"]
let ty_map ty1 ty2 = Why3.Ty.ty_app ts_map [ty1; ty2]
let fs_get = Why3.Theory.ns_find_ls map_theory.Why3.Theory.th_export ["get"]

let t_get m a = Why3.Term.t_app_infer fs_get [m; a]
let t_get1 m a = t_get m (Why3.Term.t_tuple [a])


(** booleans **)
let bool_theory = Why3.Env.read_theory env ["bool"] "Bool"
let fs_notb = Why3.Theory.ns_find_ls bool_theory.Why3.Theory.th_export ["notb"]
let fs_andb = Why3.Theory.ns_find_ls bool_theory.Why3.Theory.th_export ["andb"]


(** reals **)
let ty_real = Why3.Ty.ty_real

let real_theory = Why3.Env.read_theory env ["real"] "Real"
let real_infix_theory = Why3.Env.read_theory env ["real"] "RealInfix"
let real_pow_theory = Why3.Env.read_theory env ["real"] "PowerInt"
let find_op_fromm_real_infix name =
  Why3.Theory.ns_find_ls real_infix_theory.Why3.Theory.th_export [name]
let ps_real_le = find_op_fromm_real_infix "infix <=."
let ps_real_lt = find_op_fromm_real_infix "infix <."
let ps_real_ge = find_op_fromm_real_infix "infix >=."
let ps_real_gt = find_op_fromm_real_infix "infix >."
let fs_real_plus = find_op_fromm_real_infix "infix +."
let fs_real_minus = find_op_fromm_real_infix "infix -."
let fs_real_uminus = find_op_fromm_real_infix "prefix -."
let fs_real_mult = find_op_fromm_real_infix "infix *."
let fs_real_div = find_op_fromm_real_infix "infix /."
let fs_real_pow =
  Why3.Theory.ns_find_ls real_pow_theory.Why3.Theory.th_export ["power"]

let from_int_theory = Why3.Env.read_theory env ["real"] "FromInt"
let fs_from_int =
  Why3.Theory.ns_find_ls from_int_theory.Why3.Theory.th_export ["from_int"]



(** simt related constructs **)
let simt_theory = Why3.Env.read_theory env ["simt"] "Simt"

let simt_export = simt_theory.Why3.Theory.th_export
let fs_tid_of = Why3.Theory.ns_find_ls simt_export ["tid_of"]
let fs_bid_of = Why3.Theory.ns_find_ls simt_export ["bid_of"]
let fs_bdim = Why3.Theory.ns_find_ls simt_export ["blockDim"]
let fs_gdim = Why3.Theory.ns_find_ls simt_export ["gridDim"]
let fs_x = Why3.Theory.ns_find_ls simt_export ["x"]
let fs_y = Why3.Theory.ns_find_ls simt_export ["y"]
let fs_z = Why3.Theory.ns_find_ls simt_export ["z"]
let fs_mk_dim3 = Why3.Theory.ns_find_ls simt_export ["mk dim3"]

let ts_dim3 = Why3.Theory.ns_find_ts simt_export ["dim3"]

let ty_thread =
  Why3.Ty.ty_app (Why3.Theory.ns_find_ts simt_export ["thread"]) []
let ty_block =
  Why3.Ty.ty_app (Why3.Theory.ns_find_ts simt_export ["block"]) []

let ty_local ty = ty_map ty_thread ty
let ty_shared ty = ty_map ty_block ty
let ty_global ty = ty
let ty_dim3 = Why3.Ty.ty_app ts_dim3 []


(** unit *)
let unit_theory = Why3.Theory.unit_theory
let ty_unit =
  let sym = Why3.Theory.ns_find_ts
              unit_theory.Why3.Theory.th_export ["unit"] in
  Why3.Ty.ty_app sym []


(** sum *)
let sum_theory = Why3.Env.read_theory env ["simt"] "Sum"

let sum_export = sum_theory.Why3.Theory.th_export
let fs_sum_i = Why3.Theory.ns_find_ls sum_export ["sum_i"]
let fs_sum_r = Why3.Theory.ns_find_ls sum_export ["sum_r"]

