module type OrderedType = sig
    type t
    val compare : t -> t -> int
  end

module Make (O : OrderedType) : sig
  val v_compare : O.t -> O.t -> int

  type monomial
  val m_var : O.t -> monomial
  val m_compare : monomial -> monomial -> int
  val m_mult : monomial -> monomial -> monomial

  type polynomial
  val p_repr : polynomial -> (O.t list * Why3.BigInt.t) list
  val of_repr : (O.t list * Why3.BigInt.t) list -> polynomial
  val p_var : O.t -> polynomial
  val p_bigint : Why3.BigInt.t -> polynomial
  val p_int : int -> polynomial
  val p_zero : polynomial
  val p_is_const : polynomial -> bool
  val p_const_part : polynomial -> Why3.BigInt.t
  val p_equal : polynomial -> polynomial -> bool
  val p_add : polynomial -> polynomial -> polynomial
  val p_neg : polynomial -> polynomial
  val p_sub : polynomial -> polynomial -> polynomial
  (* val p_t_mult : polynomial -> monomial * int -> polynomial *)
  val p_mult : polynomial -> polynomial -> polynomial
  val p_contains : O.t -> polynomial -> bool

  val p_fold : (O.t -> 'a) -> (Why3.BigInt.t -> 'a) ->
             ('a -> 'a -> 'a) -> ('a -> 'a -> 'a) ->
             polynomial -> 'a

  val m_subst : O.t -> polynomial -> monomial -> polynomial
  val p_subst : O.t -> polynomial -> polynomial -> polynomial

  val p_divide : polynomial -> polynomial -> polynomial option
end
