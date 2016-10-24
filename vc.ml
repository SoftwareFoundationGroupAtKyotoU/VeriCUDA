open Why3.Term

module Varinfo = struct
  type t = Cil.varinfo
  let compare v1 v2 = compare v1.Cil.vid v2.Cil.vid
end

module VarinfoMap : (Map.S with type key = Cil.varinfo) =
  Map.Make(Varinfo)

module OrderedString = struct
  type t = string
  let compare : string -> string -> int = compare
end

module StrMap : (Map.S with type key = string) =
  Map.Make(OrderedString)


type assignment_info = {
  a_newvar : lsymbol;
  a_oldvar : lsymbol;
  a_mask : term -> term;
  a_index : term -> term;
  a_rhs : term -> term;
  a_mkind : Formula.var_kind;
}

type declaration =
  | VarDecl of lsymbol        (* automatically generated variable *)
  | AxiomDecl of term         (* automatically generated assumption *)
  | AsgnDecl of assignment_info (* assignment *)

type vc = {
  (* vc_asgn : assignment_info list; *)
  vc_decls : declaration list;
  vc_goal : term;
  vc_name : string option;
}

let check_barrier_divergence = ref false
let check_race_freedom = ref false
