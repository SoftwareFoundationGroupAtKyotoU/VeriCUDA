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
  | PTAt of parsetree * parsetree (* ? *)
  | PTAcc of string * parsetree list
  | PTConst of const * xyz

let pt_true = PTTrue
let pt_false = PTFalse
let pt_impl asmps concl  = PTImpl (asmps, concl)
let pt_or es = PTOr es
let pt_and es = PTAnd es
let pt_not a = PTNot a
let pt_forall x ts a = PTForall (x, ts, a)
let pt_forall_threads x ts a = PTForallThread (x, ts, a)
let pt_exists x ts a = PTExists (x, ts, a)
let pt_exists_threads x ts a = PTExistsThread (x, ts, a)
let pt_eq a b = PTEq (a, b)
let pt_neq a b = PTNeq (a, b)
let pt_lt a b = PTLT (a, b)
let pt_le a b = PTLE (a, b)
let pt_gt a b = PTGT (a, b)
let pt_ge a b = PTGE (a, b)
let pt_plus a b = PTPlus (a, b)
let pt_minus a b = PTMinus (a, b)
let pt_mult a b = PTMult (a, b)
let pt_div a b = PTDiv (a, b)
let pt_mod a b = PTMod (a, b)
let pt_pow a b = PTPow (a, b)
let pt_uminus a = PTUminus a
let pt_int n = PTInt n
let pt_sum i a b c = PTSum (i, a, b, c)
let pt_act a = PTAct a
let pt_at a t = PTAt (a, t)
let pt_acc x es = PTAcc (x, es)
let pt_const c d = PTConst (c, d)

let sprintf = Printf.sprintf

let rec string_of_ptree = function
  | PTTrue -> "True"
  | PTFalse -> "False"
  | PTImpl (xs, x) ->
     sprintf "impl ([%s], %s)" (string_of_ptree_list xs) (string_of_ptree x)
  | PTOr xs -> sprintf "or ([%s])" @@ string_of_ptree_list xs
  | PTAnd xs -> sprintf "and ([%s])" @@ string_of_ptree_list xs
  | PTNot x -> sprintf "not (%s)" @@ string_of_ptree x
  | PTForall (v, ts, x) -> sprintf "forall (%s, %s, %s)" v
                                   (string_of_ptree_list ts) (string_of_ptree x)
  | PTForallThread (v, ts, x) -> sprintf "forall_t (%s, %s, %s)" v
                                         (string_of_ptree_list ts) (string_of_ptree x)
  | PTExists (v, ts, x) -> sprintf "exists (%s, %s, %s)" v
                                   (string_of_ptree_list ts) (string_of_ptree x)
  | PTExistsThread (v, ts, x) -> sprintf "exists_t (%s, %s, %s)" v
                                         (string_of_ptree_list ts) (string_of_ptree x)
  | PTEq (x, x') -> sprintf "eq (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTNeq (x, x') -> sprintf "neq (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTLT (x, x') -> sprintf "lt (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTGT (x, x') -> sprintf "gt (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTLE (x, x') -> sprintf "le (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTGE (x, x') -> sprintf "ge (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTPlus (x, x') -> sprintf "plus (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTMinus (x, x') -> sprintf "minus (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTMult (x, x') -> sprintf "mult (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTDiv (x, x') -> sprintf "div (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTMod (x, x') -> sprintf "mod (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTPow (x, x') -> sprintf "pow (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTUminus x -> sprintf "uminus (%s)" (string_of_ptree x)
  | PTInt n -> sprintf "int (%d)" n
  | PTSum (x, a, b, c) ->
     sprintf "sum (%s, %s, %s, %s)"
             x (string_of_ptree a) (string_of_ptree b) (string_of_ptree c)
  | PTAct x -> sprintf "active (%s)" (string_of_ptree x)
  | PTAt (x, x') -> sprintf "at (%s, %s)" (string_of_ptree x) (string_of_ptree x')
  | PTAcc (x, xs) -> sprintf "acc (%s, %s)" x (string_of_ptree_list xs)
  | PTConst (c, d) -> sprintf "%s.%s"
                              (match c with
                               | TID -> "threadIdx"
                               | BID -> "blockIdx"
                               | BDIM -> "blockDim"
                               | GDIM -> "gridDim")
                              (match d with
                                 X -> "x" | Y -> "y" | Z -> "z")
and string_of_ptree_list xs = 
  "[" ^ String.concat "; " (List.map string_of_ptree xs) ^ "]"
