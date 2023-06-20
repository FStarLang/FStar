module Pulse.Checker.Inference

module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Framing
open Pulse.Checker.VPropEquiv
module P = Pulse.Syntax.Printer

module RT = FStar.Reflection.Typing
module RUtil = Pulse.Reflection.Util

let uvar_id = nat
let uvar = uvar_id & ppname

let uvar_eq (u1 u2:uvar) : b:bool { b <==> (u1 == u2)} =
  fst u1 = fst u2

let uvar_to_string (num, pp) =
  FStar.Printf.sprintf "?%s_%d" (T.unseal pp.name) num

let range_of_uvar (u:uvar) : range = (snd u).range

let embedded_uvar_prefix = "__pulse_embedded_uvar__"

let is_uvar_r (t:R.term) : option uvar = 
    match R.inspect_ln t with
    | R.Tv_UInst fv [u] -> (
      match R.inspect_fv fv with
      | [prefix; name] -> 
        if prefix = embedded_uvar_prefix
        then match R.inspect_universe u with
              | R.Uv_BVar n -> Some (n, mk_ppname (T.seal name) (T.range_of_term t))
              | _ -> None
        else None
      | _ -> None
    )
    | _ -> None

let is_uvar (t:term) : option uvar =
  match t.t with
  | Tm_FStar r -> is_uvar_r r
  | _ -> None

let wrap_nat_to_uvar (name:string) (r:range) (n:nat) : term =
  let tm = R.pack_ln (R.Tv_UInst (R.pack_fv [embedded_uvar_prefix; name]) [R.pack_universe (R.Uv_BVar n)]) in
  tm_fstar tm r

let gen_uvar (name:ppname) =
  let n = T.fresh () in
  assume (n >= 0);  // TODO: relying on the implementation of fresh in the typechecker
  let nm = T.unseal name.name in
  (n, name), wrap_nat_to_uvar nm name.range n

let rec gen_uvars (g:env) (t_head:term) : T.Tac (list uvar & comp) =
  let ropt = is_arrow t_head in
  match ropt with
  | Some (b, Some Implicit, c_rest) -> (
    let n, tm = gen_uvar b.binder_ppname in
    let c_rest = open_comp_with c_rest tm in
    match c_rest with
    | C_ST c
    | C_STAtomic _ c
    | C_STGhost _ c ->
      [n], c_rest
    | C_Tot t ->
      let n_rest, comp_typ = gen_uvars g t in
      n::n_rest, comp_typ
  )
  | _ ->
   fail g None (FStar.Printf.sprintf "gen_uvars: unexpected t_head: %s"
                                  (P.term_to_string t_head))

let rec check_valid_solution (g:env) (n:uvar) (t:term) (uv_sols:solution)
  : T.Tac solution =

  match uv_sols with
  | [] -> [n, t]
  | (n', t')::tl ->
    if uvar_eq n n'
    then if eq_tm t t' then uv_sols
         else fail g None "check_valid_solution failed"
    else (n', t')::(check_valid_solution g n t tl)

let uvar_index (t:term{Some? (is_uvar t)}) : uvar =
  Some?.v (is_uvar t)

let is_reveal_uvar (t:term) : option (universe & term & term) =
  match is_pure_app t with
  | Some (hd, None, arg) ->
    (match is_pure_app hd with
     | Some (hd, Some Implicit, ty) ->
       if Some? (is_uvar arg)
       then match is_fvar hd with
           | Some (l, [u]) ->
             if l = RUtil.reveal_lid
             then Some (u, ty, arg)
             else None
           | _ -> None
       else None
     | _ -> None)
  | _ -> None

let is_reveal (t:term) : bool =
  match leftmost_head t with
  | Some hd ->
    (match is_fvar hd with
     | Some (l, [_]) -> l = RUtil.reveal_lid
     | _ -> false)
  | _ -> false

let rec match_typ (g:env) (t1 t2:term) (uv_sols:solution)
  : T.Tac solution =

  match is_reveal_uvar t1, is_reveal t2 with
  | Some (u, ty, t), false ->
    check_valid_solution g (uvar_index t) (mk_hide u ty t2) uv_sols
  | _ ->
    if Some? (is_uvar t1)
    then check_valid_solution g (uvar_index t1) t2 uv_sols
    else if Some? (is_uvar t2)
    then fail g None "match_typ: t2 is a uvar"
    else match t1.t, t2.t with
         | Tm_Pure t1, Tm_Pure t2 ->
           match_typ g t1 t2 uv_sols
    
         | _, _ ->
           match is_pure_app t1, is_pure_app t2 with
           | Some (head1, arg_qual1, arg1), Some (head2, arg_qual2, arg2) ->
             if arg_qual1 = arg_qual2
             then let uv_sols = match_typ g head1 head2 uv_sols in
                  match_typ g arg1 arg2 uv_sols
             else uv_sols

           | _, _ -> uv_sols

let rec atomic_vprop_has_uvar (t:term) : bool =
  if Some? (is_uvar t) then true
  else match t.t with
       | Tm_Pure arg -> atomic_vprop_has_uvar arg
       | Tm_Emp -> false
       | _ ->
         match is_pure_app t with
         | Some (head, _, arg) ->
           assume (head << t /\ arg << t);
           atomic_vprop_has_uvar head || atomic_vprop_has_uvar arg
         | _ -> false

let rec atomic_vprops_may_match (t1:term) (t2:term) : bool =
  if Some? (is_reveal_uvar t1) && not (is_reveal t2)
  then true
  else if Some? (is_uvar t1) then true
  else match t1.t, t2.t with
       | Tm_Pure x, Tm_Pure y ->
         atomic_vprops_may_match x y
       | _, _ ->
         match is_pure_app t1, is_pure_app t2 with
         | Some (head1, q1, arg1), Some (head2, q2, arg2) ->
           assume (head1 << t1 /\ arg1 << t1);
           assume (head2 << t2 /\ arg2 << t2);
           atomic_vprops_may_match head1 head2 &&
           q1 = q2 &&
           atomic_vprops_may_match arg1 arg2
         | _, _ -> eq_tm t1 t2

let infer_one_atomic_vprop (g:env) (t:term) (ctxt:list term) (uv_sols:solution)
  : T.Tac solution =

  if atomic_vprop_has_uvar t
  then
    let matching_ctxt = List.Tot.filter (fun ctxt_vp -> atomic_vprops_may_match t ctxt_vp) ctxt in
    // T.print (FStar.Printf.sprintf "infer_one_atomic_vprop %s, found %d matching candidates\n"
    //            (P.term_to_string t)
    //            (List.Tot.length matching_ctxt));
    if List.Tot.length matching_ctxt = 1
    then
      // let _ = T.print (FStar.Printf.sprintf "infer_one_atomic_vprop: matching %s and %s with %d exisiting solutions\n"
      //                    (P.term_to_string t)
      //                    (P.term_to_string (List.Tot.hd matching_ctxt))
      //                    (List.Tot.length uv_sols)) in 
      let uv_sols = match_typ g t (List.Tot.hd matching_ctxt) uv_sols in
      // T.print (FStar.Printf.sprintf "post matching, uv_sols has %d solutions\n"
      //            (List.Tot.length uv_sols))
      uv_sols
    else uv_sols
  else uv_sols

let union_ranges (r0 r1:range) : T.Tac range = r0
let with_range (t:st_term') (r:range) : st_term = { term = t; range = r}

let rec rebuild_head (g:env) (head:term) (uvs:list uvar) (uv_sols:solution) (r:range)
  : T.TacH st_term (requires fun _ -> List.Tot.length uvs > 0)
                   (ensures fun _ _ -> True) =
  let hd::tl = uvs in
  let ropt = List.Tot.find (fun (n1, _) -> uvar_eq hd n1) uv_sols in
  match ropt with
  | None ->
    fail g (Some r)
           (FStar.Printf.sprintf
              "inference failed in building head, no solution for %s\n"
              (uvar_to_string hd))
  | Some (_, t2) ->
    match tl with
    | [] -> with_range (Tm_STApp { head; arg_qual= Some Implicit; arg=t2 })
                       r
    | _ ->
      let app_node = tm_pureapp head (Some Implicit) t2 in
      rebuild_head g app_node tl uv_sols r


let print_solutions (l:solution)
  : T.Tac string
  = String.concat "\n"
      (T.map #(uvar & term) #string
        (fun (u, t) ->
          Printf.sprintf "%s := %s" 
                       (uvar_to_string u)
                       (P.term_to_string t))
        l)


let find_solution (sol:solution) (t:uvar)
  : option term
  = let r = List.Tot.find (fun (u, _) -> uvar_eq u t) sol in
    match r with
    | None -> None
    | Some (_, t) -> Some t


let try_inst_uvs_in_goal (g:env) (ctxt:term)
                         (goal:vprop)
  : T.Tac solution
  = let uv_sols = [] in
    let goal_list = vprop_as_list goal in
    let ctxt_list = vprop_as_list ctxt in
    let uv_sols =
      T.fold_left
        (fun uv_sols goal_vprop ->
          infer_one_atomic_vprop g goal_vprop ctxt_list uv_sols)
        uv_sols
        goal_list
    in
    let sols = uv_sols in
    sols



let infer
  (g:env)
  (head:term)
  (t_head:term)
  (ctxt_pre:term)
  (r:range)
  : T.Tac st_term =
  let g = push_context g "infer" r in
  let uvs, pre =
    let uvs, comp = gen_uvars g t_head in
    match comp with
    | C_ST st_comp
    | C_STAtomic _ st_comp
    | C_STGhost _ st_comp -> uvs, st_comp.pre
    | _ -> fail g (Some r) "infer:unexpected comp type"
  in

  if List.Tot.length uvs = 0
  then fail g (Some r) "Inference did not find anything to infer"
  else begin
    // T.print (FStar.Printf.sprintf "infer: generated %d uvars,\n\
    //                                ctx: {\n%s\n}\n\
    //                                st_comp.pre:{\n%s\n}"
    //            (List.Tot.length uvs)
    //            (P.term_list_to_string "\n" (vprop_as_list ctxt_pre))
    //            (P.term_list_to_string "\n" (vprop_as_list pre)));
    let uv_sols = try_inst_uvs_in_goal g ctxt_pre pre in
    // T.print (Printf.sprintf "Got solutions: {\n%s\}"  (print_solutions uv_sols));
    let head = rebuild_head g head uvs uv_sols r in
    // T.print (Printf.sprintf "Rebuilt head= %s" (P.st_term_to_string head));
    head
  end

let solutions_to_string sol = print_solutions sol

let apply_sol (sol:solution) (t:R.term) =
  let solve_uvar (t:R.term) : T.Tac R.term = 
    match is_uvar_r t with
    | None -> t
    | Some n ->
      match find_solution sol n with
      | None -> t
      | Some ({t=Tm_FStar t}) -> t
      | Some t -> Pulse.Elaborate.Pure.elab_term t
  in
  FStar.Tactics.Visit.visit_tm solve_uvar t
 
let rec apply_solution (sol:solution) (t:term)
  : T.Tac term
  = let w (t':term') : term = Pulse.Syntax.Base.with_range t' t.range in
    match t.t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> t

    | Tm_FStar t ->
      let t = apply_sol sol t in
      assume (not_tv_unknown t);
      w (Tm_FStar t)

    | Tm_Pure p ->
      w (Tm_Pure (apply_solution sol p))

    | Tm_Star l r ->
      w (Tm_Star (apply_solution sol l)
                 (apply_solution sol r))
              
    | Tm_ExistsSL u b body ->
      w (Tm_ExistsSL u { b with binder_ty = apply_solution sol b.binder_ty }
                       (apply_solution sol body))
       
    | Tm_ForallSL u b body ->
      w (Tm_ForallSL u { b with binder_ty = apply_solution sol b.binder_ty }
                       (apply_solution sol body))

let contains_uvar_r (t:R.term) =
    let is_uvar (t:R.term) : T.Tac R.term = 
      if Some? (is_uvar_r t)
      then T.fail "found uvar"
      else t
    in
    T.or_else
      (fun _ -> 
          let _ = T.visit_tm is_uvar t in
          false)
      (fun _ -> true)


let rec contains_uvar (t:term)
  : T.Tac bool
  = match t.t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> false
      
    | Tm_Pure p ->
      (contains_uvar p)
      
    | Tm_Star l r ->
      if contains_uvar l then true
      else contains_uvar r
              
    | Tm_ExistsSL u t body ->
      if contains_uvar t.binder_ty then true
      else contains_uvar body
       
    | Tm_ForallSL u t body ->
      if contains_uvar t.binder_ty then true
      else contains_uvar body
                    
    | Tm_FStar t ->
      contains_uvar_r t

let try_unify (g:env) (l r:term) = match_typ g l r []

module RF = FStar.Reflection.Formula

let is_eq2 (t:R.term) : option (R.term & R.term) =
  let head, args = R.collect_app_ln t in
  match R.inspect_ln head, args with
  | R.Tv_FVar fv, [_; (a1, _); (a2, _)]
  | R.Tv_UInst fv _, [_; (a1, _); (a2, _)] -> 
    let l = R.inspect_fv fv in
    if l = ["Pulse"; "Steel"; "Wrapper"; "eq2_prop"] ||
       l = ["Prims"; "eq2"]
    then Some (a1, a2)
    else None
  | _ -> None

let try_solve_pure_equalities (g:env) (p:term) : T.Tac solution =
  let rec aux (sol:solution) (t:R.term) : T.Tac solution =
    let open RF in
    let t = apply_sol sol t in
    let f = RF.term_as_formula' t in
    let handle_eq (t0 t1:R.term) =
      let contains0 = contains_uvar_r t0 in
      let contains1 = contains_uvar_r t1 in
      if contains0 || contains1
      then (
        assume (not_tv_unknown t0 /\ not_tv_unknown t1);
        try_unify g (tm_fstar t0 FStar.Range.range_0)
                    (tm_fstar t1 FStar.Range.range_0) @ sol
      )
      else sol
    in
    match f with
    | Comp  (Eq _) t0 t1 -> handle_eq t0 t1
    | And t0 t1 -> aux (aux sol t0) t1
    | _ ->
      match is_eq2 t with
      | Some (t0, t1) -> handle_eq t0 t1
      | _ -> sol 
  in
  match p.t with
  | Tm_FStar t -> aux [] t
  | _ -> []