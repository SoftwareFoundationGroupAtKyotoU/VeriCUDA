open Why3.Term
open Why3api
open Why3util
open Formula
open Utils
open Vc

(** ---------------- eliminate assignment *)
(* assignment is replaced with a variable declaration;
 * when a loop is encountered, we duplicate the sequence
 * generated so far, and generate three sequences corresponding to:
 * 1. loop invariant at the loop entry
 * 2. loop invariant preservation
 * 3. the rest of the program, starting with
 *    the declaration of new variables corresponding to variables
 *    modified during the loop iteration, followed by the declaration
 *    of axioms that states that the invariant is true at exit,
 *    and the encodings of the rest of the program
 * *)

(* Newly introduced variables corresponding to assignments
 * are eliminated at this stage, by rewriting the goal.  *)

let decompose_get t =
  match t.t_node with
  | Tapp (lsym, [m; a]) when ls_equal fs_get lsym
    -> Some (m, a)
  | _ -> None

let match_access_to_glob x t bvars =
  (* Tests if [t] matches [get x ts] for some [ts],
   * where all variables in [bvars] do not occur in [ts]. *)
  match decompose_get t with
  | Some ({ t_node = Tapp (lsym, []) }, ts)
       when ls_equal lsym x && Mvs.set_disjoint (t_vars ts) bvars
    -> Some ts
  | _ -> None

let match_access_to_nonglob x t bvars =
  (* Tests if [t] matches [get (get x p) ts] for some [p] and [ts],
   * where all variables in [bvars] do not occur in [ts]. *)
  match decompose_get t with
  | Some (t', ts) when Mvs.set_disjoint (t_vars ts) bvars
    -> begin match decompose_get t' with
       | Some ({ t_node = Tapp (lsym, []) }, p)
          when ls_equal lsym x && Mvs.set_disjoint (t_vars p) bvars
         -> Some (p, ts)
       | _ -> None
       end
  | _ -> None

let rec find_access matcher (x : lsymbol) (t : term) (bvars : int Mvs.t) =
  (* Finds a subterm of [t] of the form [get x ts] and returns it.
   * [x] is intended to be a representation of the value of a global
   * variable (a pointer to the global memory) at some program point.
   * [x] must not occur in the triggers.
   * [ts] must be visible from a certain point outside the scope where
   * [t] resides in; [bvars] specifies variables which are not visible
   * from the scope where the call of this function takes place.  *)
  match matcher x t bvars with
  | Some ts -> Some (t, ts)
  | None ->
     match t.t_node with
     (* | Tvar vsym -> if Why3.Ident.id_equal x vsym.vs_name
      *                then Some t else None *)
     | Tvar _             (*  [x] is an lsymbol, so this never matches *)
     | Tconst _ -> None
     | Tapp (_, ts) -> find_access' matcher x ts bvars
     | Tif (t1, t2, t3) ->
        find_access' matcher x [t1; t2; t3] bvars
     | Tlet (t, tb) ->
        let (vsym, t) = t_open_bound tb in
        let bvars' = Mvs.add vsym 1 bvars in
        find_access matcher x t bvars'
     | Tcase (t, tbs) -> not_implemented "case"
     | Teps tb ->
        let (vs, t') = t_open_bound tb in
        find_access matcher x t' (Mvs.add vs 1 bvars)
     | Tquant (_, tq) ->
        let (vsyms, trigger, t) = t_open_quant tq in
        if !Options.use_triggers_flag then
          List.iter (List.iter (fun t -> assert (not (t_ls_occurs x t))))
                    trigger
        else
          assert (trigger = []);
        let bvars' = List.fold_left (fun bvs v -> Mvs.add v 1 bvs) bvars vsyms in
        find_access matcher x t bvars'
     | Tbinop (_, t1, t2) ->
        find_access' matcher x [t1; t2] bvars
     | Tnot t -> find_access matcher x t bvars
     | Ttrue
     | Tfalse -> None
and find_access' matcher x ts bvars =
  List.fold_left (fun r t -> match r with
                             | Some _ -> r
                             | None -> find_access matcher x t bvars)
                 None ts

let find_access_to_glob x t bvars =
  find_access match_access_to_glob x t bvars

let find_access_to_nonglob x t bvars =
  find_access match_access_to_nonglob x t bvars

let expand_weak { a_newvar = x'; a_mkind = mkind; a_oldvar = x;
                  a_mask = m; a_index = es; a_rhs = e }
                fml =
  (* Transform an occurrence of [x'] with appropriate term,
   * satisfying appropriate conditions.
   * Since there can be multiple clauses in the definition of [x']
   * (updated case and not updated case) multiple copies of [fml]
   * may appear in the result.
   * The returned formula implies the original, but the converse
   * is not necessarily true in case the assignment races.
   *
   * This function should be optimizated in several cases.
   * (e.g. when [x'] is a local scalar)  *)
  match mkind with
  | Local
  | Formal ->
     begin match find_access_to_nonglob x' fml Mvs.empty with
           | None ->
              (* do nothing at this moment. *)
              fml, false
           | Some (t, (th, ts)) ->
              (* if m == Formula.t_is_valid_thread &&
               *      t_equal ts (t_tuple [])
               * then
               *   t_replace t (e th) fml, true
               * else *)
                t_or (t_and (t_implies (m th)
                                       (t_neq_tp (es th) ts))
                            (t_replace t (t_get (if mkind = Formal
                                                 then t_ls x
                                                 else t_get (t_ls x) th)
                                                ts) fml))
                     (t_and (t_and (m th) (t_equ_tp (es th) ts))
                            (t_replace t (e th) fml))
              , true
     end
  | Shared ->
     begin match find_access_to_nonglob x' fml Mvs.empty with
           | None -> fml, false
           | Some (t, (b, ts)) ->
              let l_id = Why3.Ident.id_fresh "l" in
              let l_sym = create_vsymbol l_id ty_dim3 in
              let l = t_var l_sym in
              let th = t_tuple [b; l] in
              t_or (t_and (t_forall_close [l_sym] []
                                          (t_implies
                                             (m th)
                                             (t_neq_tp (es th) ts)))
                          (t_replace t (t_get (t_get (t_ls x) b) ts) fml))
                   (t_exists_close [l_sym] []
                                   (t_and
                                      (m th)
                                      (t_and
                                         (t_equ_tp (es th) ts)
                                         (t_replace t (e th) fml))))
              , true
     end
  | Global ->
     begin match find_access_to_glob x' fml Mvs.empty with
           | None -> fml, false
           | Some (t, ts) ->
              let th_sym = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in
              let th = t_var th_sym in
              t_or (t_and (t_forall_close [th_sym] []
                                          (t_implies
                                             (m th)
                                             (t_neq_tp (es th) ts)))
                          (t_replace t (t_get (t_ls x) ts) fml))
                   (t_exists_close [th_sym] []
                                   (t_and
                                      (m th)
                                      (t_and
                                         (t_equ_tp (es th) ts)
                                         (t_replace t (e th) fml))))
              , true
     end

let expand_strong { a_newvar = x'; a_mkind = mkind; a_oldvar = x;
                    a_mask = m; a_index = es; a_rhs = e }
                  fml =
  (* Similar to [expand_weak], but this version returns a stronger
   * formula, rather than weaker one. *)
  match mkind with
  | Local
  | Formal ->
     begin match find_access_to_nonglob x' fml Mvs.empty with
           | None ->
              (* do nothing at this moment. *)
              fml, false
           | Some (t, (th, ts)) ->
              (* if m == Formula.t_is_valid_thread &&
               *      t_equal ts (t_tuple [])
               * then
               *   t_replace t (e th) fml, true
               * else *)
                t_and (t_implies
                         (t_implies (m th)
                                    (t_neq_tp (es th) ts))
                         (t_replace t (t_get (if mkind = Formal
                                              then (t_ls x)
                                              else (t_get (t_ls x) th))
                                             ts) fml))
                      (t_implies (t_and (m th) (t_equ_tp (es th) ts))
                                 (t_replace t (e th) fml))
              , true
     end
  | Shared ->
     begin match find_access_to_nonglob x' fml Mvs.empty with
           | None -> fml, false
           | Some (t, (b, ts)) ->
              let l_id = Why3.Ident.id_fresh "l" in
              let l_sym = create_vsymbol l_id ty_dim3 in
              let l = t_var l_sym in
              let th = t_tuple [b; l] in
              t_and
                (t_implies (t_forall_close [l_sym] []
                                           (t_implies
                                              (m th)
                                              (t_neq_tp (es th) ts)))
                           (t_replace t (t_get (t_get (t_ls x) b) ts) fml))
                (t_forall_close [l_sym] []
                                (t_implies
                                   (m th)
                                   (t_implies
                                      (t_equ_tp (es th) ts)
                                      (t_replace t (e th) fml))))
              , true
     end
  | Global ->
     begin match find_access_to_glob x' fml Mvs.empty with
           | None -> fml, false
           | Some (t, ts) ->
              let th_sym = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in
              let th = t_var th_sym in
              t_and (t_implies (t_forall_close [th_sym] []
                                               (t_implies
                                                  (m th)
                                                  (t_neq_tp (es th) ts)))
                               (t_replace t (t_get (t_ls x) ts) fml))
                    (t_forall_close [th_sym] []
                                    (t_implies
                                       (m th)
                                       (t_implies
                                          (t_equ_tp (es th) ts)
                                          (t_replace t (e th) fml))))
              , true
     end

let expand a sign fml =
  (* Eliminate assignment [a], if there is any occurrence in [fml] of
   * the result of this assignment. *)
  if sign then expand_strong a fml else expand_weak a fml

let rec eliminate_assignment ainfo sign fml =
  (* Expand a subterm [x'] of [fml] into the result of x[es]:=e with m.
   * Any argument [ts] to [x'] must not contain any variable bound inside
   * [fml] since if we do not take bound variables into account,
   * such variables would appear freely in the resulting formula.
   *)
  if not (is_formula fml) then fml
  else
    let fml', b = expand ainfo sign fml in
    if b then eliminate_assignment ainfo sign fml'
    else
      (* There is no more subterms that can be eliminated at this level,
       * but we have to process subformulas.
       * Current implementation is redundant; only the cases of
       * quantifiers are essential, so we can separate traversal and
       * actual elimination function for optimization. *)
      match fml.t_node with
      | Tquant (q, tq) ->
         begin
           match t_open_quant tq with
           | ([vs], [], t') ->
              begin
                match t'.t_node with
                | Tbinop (op, t1, t2)
                     when not (t_ls_occurs ainfo.a_newvar t1) &&
                            ((q = Tforall && op = Timplies) ||
                               (q = Texists && op = Tand)) ->
                   (* Simplify guard formula; probably there are better
                    * way to do this. *)
                   let t2' = t_replace_simp t1 t_true @@
                               eliminate_assignment ainfo sign t2 in
                   t_quant_close_guard q [vs] [] t1 t2'
                | _ -> t_map_sign (eliminate_assignment ainfo) sign fml
              end
           | _ -> t_map_sign (eliminate_assignment ainfo) sign fml
         end
      | _ ->
         t_map_sign (eliminate_assignment ainfo) sign fml

let formula_of_assignment
      { a_newvar = x'; a_mkind = mkind;
        a_oldvar = x; a_mask = m; a_index = es; a_rhs = e } =
    (* Simply translate `assign' into a why3 formula. *)
    match mkind with
    | Local
    | Formal ->
       let th_sym = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in
       let th = t_var th_sym in
       let mask = m th in
       let index = es th in
       let ns_syms =
         match index.t_ty with
         | Some { Why3.Ty.ty_node = Why3.Ty.Tyapp (ts, tys) }
              when Why3.Ty.ts_equal ts (Why3.Ty.ts_tuple (List.length tys))
           ->
            List.map (create_vsymbol (Why3.Ident.id_fresh "n")) tys
         | _ ->
            implementation_error "array index is not a tuple"
       in
       let ns = t_tuple @@ List.map t_var ns_syms in
       t_forall_close
         (th_sym :: ns_syms)
         (if !Options.use_triggers_flag then [[(t_get (t_get (t_ls x') th) ns)]] else [])
         (t_implies_simp
            (t_is_valid_thread th)
            (t_and_simp
               (t_implies_simp
                  (t_and_simp mask (t_equ_tp index ns))
                  (t_equ_simp
                     (t_get (t_get (t_ls x') th) ns)
                     (e th)))
               (t_implies_simp
                  (t_not_simp
                     (t_and_simp mask (t_equ_tp index ns)))
                  (t_equ_simp
                     (t_get (t_get (t_ls x') th) ns)
                     (t_get (if mkind = Formal then (t_ls x)
                             else (t_get (t_ls x) th))
                            ns)))))
    | Shared ->
       let l_sym = create_vsymbol (Why3.Ident.id_fresh "l") ty_dim3 in
       let l = t_var l_sym in
       let b_sym = create_vsymbol (Why3.Ident.id_fresh "b") ty_dim3 in
       let b = t_var b_sym in
       let th = t_tuple [b; l] in
       let mask = m th in
       let index = es th in
       let ns_syms =
         match index.t_ty with
         | Some { Why3.Ty.ty_node = Why3.Ty.Tyapp (ts, tys) }
              when Why3.Ty.ts_equal ts (Why3.Ty.ts_tuple (List.length tys))
           ->
            List.map (create_vsymbol (Why3.Ident.id_fresh "n")) tys
         | _ ->
            implementation_error "array index is not a tuple"
       in
       let ns = t_tuple @@ List.map t_var ns_syms in
       t_forall_close
         (b_sym :: ns_syms)
         (if !Options.use_triggers_flag then [[(t_get (t_get (t_ls x') b) ns)]] else [])
         (* We assume the mask implies the validity of the thread.
          * So we don't need the validity condition on [b] explicitly
          * in the first clause, but we do need it in the second. *)
         (t_or_simp
            (t_exists_close
               [l_sym] []
               (t_and_simp
                  (t_and_simp mask (t_equ_simp index ns))
                  (t_equ_simp
                     (t_get (t_get (t_ls x') b) ns)
                     (e th))))
            (t_implies_simp
               (t_is_valid_bid b)
               (t_and
                  (t_forall_close
                     [l_sym] []
                     (t_not_simp
                        (t_and_simp mask (t_equ_simp index ns))))
                  (t_equ_simp
                     (t_get (t_get (t_ls x') b) ns)
                     (t_get (t_get (t_ls x) b) ns)))))
    | Global ->
       let th_sym = create_vsymbol (Why3.Ident.id_fresh "t") ty_thread in
       let th = t_var th_sym in
       let mask = m th in
       let index = es th in
       let ns_syms =
         match index.t_ty with
         | Some { Why3.Ty.ty_node = Why3.Ty.Tyapp (ts, tys) }
              when Why3.Ty.ts_equal ts (Why3.Ty.ts_tuple (List.length tys))
           ->
            List.map (create_vsymbol (Why3.Ident.id_fresh "n")) tys
         | _ ->
            implementation_error "array index is not a tuple"
       in
       let ns = t_tuple @@ List.map t_var ns_syms in
       t_forall_close
         ns_syms
         (if !Options.use_triggers_flag then [[(t_get (t_ls x') ns)]] else [])
         (t_or_simp
            (t_exists_close
               [th_sym] []
               (t_and_simp
                  (t_and_simp mask (t_equ_tp index ns))
                  (t_equ_simp (t_get (t_ls x') ns) (e th))))
            (t_and_simp
               (t_forall_close
                  [th_sym] []
                  (t_not_simp (t_and_simp mask (t_equ_tp index ns))))
               (t_equ_simp (t_get (t_ls x') ns) (t_get (t_ls x) ns))))

(* ---------------- vc -> task *)
let split_vc_decls decls =
  List.fold_right
    (fun d (lss, axs, asgns) ->
     match d with
     | VarDecl ls -> (ls :: lss, axs, asgns)
     | AxiomDecl (a, name) -> (lss, (a, name) :: axs, asgns)
     | AsgnDecl a -> (lss, axs, a :: asgns))
    decls ([], [], [])

(* eliminate assignments in axioms/goal *)
let eliminate_assignment_from_vc vc inline =
  if inline then
    let (_, _, asgns) = split_vc_decls vc.vc_decls in
    let elim_a sign f a =
      debug "eliminating variable %a@." Why3.Pretty.print_ls a.a_newvar;
      let f' = eliminate_assignment a sign f
               |> simplify_formula in
      if Why3.Term.t_occurs (t_ls a.a_newvar) f'
      then warn "failed to eliminate variable %a@." Why3.Pretty.print_ls a.a_newvar;
      f' in
    let elim_asgn sign f = List.fold_left (elim_a sign) f asgns in
    { vc with
      vc_decls =
        List.map (function
                   | AxiomDecl (f, name) ->
                      AxiomDecl (elim_asgn false f, name)
                   | d -> d)
                 vc.vc_decls;
      vc_goal = elim_asgn true vc.vc_goal }
  else
    { vc with
      vc_decls =
        List.map (function
                   | AsgnDecl a ->
                      let name =
                        "assign_" ^ a.a_newvar.ls_name.Why3.Ident.id_string
                      in
                      AxiomDecl (formula_of_assignment a, Some name)
                   | d -> d)
                 vc.vc_decls }

let base_task =
  let use th task = Why3.Task.use_export task th in
  let add_decl decl task = Why3.Task.add_decl task decl in
  None
  |> use Why3api.int_theory
  |> use Why3api.computerdiv_theory
  |> use Why3api.power_theory
  |> use Why3api.map_theory
  |> use Why3api.bool_theory
  |> use Why3api.unit_theory
  |> use Why3api.cuda_theory
  |> use Why3api.real_theory
  |> use Why3api.real_infix_theory
  |> use Why3api.real_pow_theory
  |> use Why3api.from_int_theory
  |> use Why3api.sum_theory
  |> add_decl @@ Why3.Decl.create_ty_decl (Why3.Ty.ts_tuple 1)
  |> add_decl @@ Why3.Decl.create_param_decl (Why3.Term.fs_tuple 1)

let task_of_vc inline vc =
  let task = ref base_task in
  let add_decl decl = task := Why3.Task.add_decl !task decl in
  let vc = eliminate_assignment_from_vc vc inline in
  let (vc_vars, vc_axiom, vc_asgn) = split_vc_decls vc.vc_decls in
  (* ---- add variable declarations *)
  List.iter (fun ls -> add_decl @@ Why3.Decl.create_param_decl ls)
            vc_vars;
  debug "Added all variable declarations@.";
  (* ---- add axioms *)
  List.iteri
    (fun n (a, name) ->
     let decl_name =
       match name with
       | None -> "vc_premise_" ^ string_of_int n
       | Some name -> name
     in
     let decl_sym = Why3.Decl.create_prsymbol
                      (Why3.Ident.id_fresh decl_name) in
     add_decl @@
       Why3.Decl.create_prop_decl Why3.Decl.Paxiom decl_sym a)
    vc_axiom;
  (* ---- add goal *)
  let goal_sym =
    let name = match vc.vc_name with
      | Some name -> name
      | None -> "goal"
    in
    Why3.Decl.create_prsymbol (Why3.Ident.id_fresh name)
  in
  add_decl @@ Why3.Decl.create_prop_decl Why3.Decl.Pgoal goal_sym vc.vc_goal;
  !task

