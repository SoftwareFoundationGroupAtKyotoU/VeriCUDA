type const = TID | BID | BDIM | GDIM
type xyz = X | Y | Z

type parsetree =
  | PTTrue
  | PTFalse
  | PTImpl of parsetree list * parsetree
  | PTOr of parsetree list
  | PTAnd of parsetree list
  | PTNot of parsetree
  | PTForall of string * parsetree list * parsetree
  | PTForallThread of string * parsetree list * parsetree
  | PTExists of string * parsetree list * parsetree
  | PTExistsThread of string * parsetree list * parsetree
  | PTEq of parsetree * parsetree
  | PTNeq of parsetree * parsetree
  | PTLT of parsetree * parsetree
  | PTGT of parsetree * parsetree
  | PTLE of parsetree * parsetree
  | PTGE of parsetree * parsetree
  | PTPlus of parsetree * parsetree
  | PTMinus of parsetree * parsetree
  | PTMult of parsetree * parsetree
  | PTDiv of parsetree * parsetree
  | PTMod of parsetree * parsetree
  | PTPow of parsetree * parsetree
  | PTUminus of parsetree
  | PTInt of int
  | PTSum of string * parsetree * parsetree * parsetree
  | PTAct of parsetree
  | PTAt of parsetree * parsetree
  | PTAcc of string * parsetree list
  | PTConst of const * xyz

val pt_true : parsetree
val pt_false : parsetree
val pt_impl : parsetree list -> parsetree -> parsetree
val pt_or : parsetree list -> parsetree
val pt_and : parsetree list -> parsetree
val pt_not : parsetree -> parsetree
val pt_forall : string -> parsetree list -> parsetree -> parsetree
val pt_forall_threads : string -> parsetree list -> parsetree -> parsetree
val pt_exists : string -> parsetree list -> parsetree -> parsetree
val pt_exists_threads : string -> parsetree list -> parsetree -> parsetree
val pt_eq : parsetree -> parsetree -> parsetree
val pt_neq : parsetree -> parsetree -> parsetree
val pt_lt : parsetree -> parsetree -> parsetree
val pt_le : parsetree -> parsetree -> parsetree
val pt_gt : parsetree -> parsetree -> parsetree
val pt_ge : parsetree -> parsetree -> parsetree
val pt_plus : parsetree -> parsetree -> parsetree
val pt_minus : parsetree -> parsetree -> parsetree
val pt_mult : parsetree -> parsetree -> parsetree
val pt_div : parsetree -> parsetree -> parsetree
val pt_mod : parsetree -> parsetree -> parsetree
val pt_pow : parsetree -> parsetree -> parsetree
val pt_uminus : parsetree -> parsetree
val pt_int : int -> parsetree
val pt_sum : string -> parsetree -> parsetree -> parsetree -> parsetree
val pt_act : parsetree -> parsetree
val pt_at : parsetree -> parsetree -> parsetree
val pt_acc : string -> parsetree list -> parsetree
val pt_const : const -> xyz -> parsetree

val string_of_ptree : parsetree -> string
