module type OrderedType = sig
    type t
    val compare : t -> t -> int
  end

module Make (O : OrderedType) = struct
  let v_compare = O.compare

  let v_equal x y = v_compare x y = 0

  type monomial = O.t list

  let m_var x = [x]

  let rec m_compare m1 m2 =
    match m1, m2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x::m1', y::m2' ->
       let c = O.compare x y in
       if c = 0 then m_compare m1' m2' else c

  let m_mult m1 m2 = List.sort O.compare (m1 @ m2)

  module I = Why3.BigInt

  type polynomial = (monomial * I.t) list

  let p_repr p = p
  let of_repr p = p

  let p_var x = [[x], I.one]
  let p_bigint n = if I.eq n I.zero then [] else [[], n]
  let p_int n = p_bigint @@ I.of_int n
  let p_zero = p_int 0

  let p_is_const p =
    match p with
    | []
    | [([], _)] -> true
    | _ -> false

  let p_const_part p =
    try ExtList.List.find_map
          (function [], n -> Some n | _, _ -> None)
          p
    with Not_found -> I.zero

  let rec p_compare p1 p2 =
    match p1, p2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | (m1, n1)::p1', (m2, n2)::p2' ->
       let c = m_compare m1 m2 in
       if c = 0 then
         match I.compare n1 n2 with
         | 0 -> p_compare p1' p2'
         | x -> x
       else c

  let p_equal p1 p2 = p_compare p1 p2 = 0

  let p_add p1 p2 =
    let p = List.sort (fun (m1, _) (m2, _) -> m_compare m1 m2) (p1 @ p2) in
    let rec reduce p = match p with
      | []
      | [_] -> p
      | (m1, n1) :: (m2, n2) :: p' ->
         match m_compare m1 m2 with
           | 0 ->
              if I.compare (I.add n1 n2) I.zero = 0 then reduce p'
              else reduce ((m1, I.add n1 n2) :: p')
           | n when n < 0 ->
              (m1, n1) :: reduce ((m2, n2) :: p')
           | _ -> assert false
    in reduce p

  let p_neg p = List.map (fun (m, n) -> (m, I.minus n)) p

  let p_sub p1 p2 = p_add p1 (p_neg p2)

  let p_t_mult p (m, n) =
    List.map (fun (m', n') -> (m_mult m m', I.mul n n')) p

  let p_mult p1 p2 =
    List.fold_left (fun p t -> p_add p (p_t_mult p1 t)) p_zero p2

  let p_contains x p =
    List.exists (fun (m, _) -> List.exists (v_equal x) m) p

  let tm_fold var int mult (m, n) =
    match m with
    | [] -> int n
    | x::m' ->
       if I.compare I.zero n = 0 then int I.zero
       else
         let r = List.fold_left mult (var x) (List.map var m') in
         if I.eq I.one n then r
         else mult (int n) r

  let p_fold var int add mult p =
    match p with
    | [] -> int I.zero
    | t::p' ->
       List.fold_left add
                      (tm_fold var int mult t)
                      (List.map (tm_fold var int mult) p')

  let rec m_subst x r m =
    (* returns m[x:=r] *)
    match m with
    | [] -> p_int 1
    | v::m' ->
       let p' = m_subst x r m' in
       if v_compare v x = 0
       then p_mult r p'
       else p_mult (p_var v) p'

  let rec p_subst x r p =
    (* returns p[x:=r] *)
    List.fold_left p_add
                   p_zero
                   (List.map (fun (m, n) ->
                              p_mult (p_bigint n) (m_subst x r m))
                             p)

  exception NotDivisible

  let m_divide (vs1, n1) vs2 n2 =
    let rec remove vs v = match vs with
      | v' :: vs' -> if v_equal v v' then vs' else v' :: remove vs' v
      | [] -> raise NotDivisible
    in
    (* the calculation of [vs] can be optimized because
     * we may assume [vs1] and [vs2] are sorted *)
    let vs = List.fold_left remove vs1 vs2 in
    let q, r = I.euclidean_div_mod n1 n2 in
    if I.eq I.zero r then (vs, q) else raise NotDivisible

  let p_divide p q =
    (* assume q is a monomial *)
    match q with
    | [vs, n] ->
       begin
         try Some (List.map (fun m -> m_divide m vs n) p)
         with NotDivisible -> None
       end
    | _ -> None

end

