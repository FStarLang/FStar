module Pulse.Checker.Inference

module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Framing
module P = Pulse.Syntax.Printer

module RT = FStar.Reflection.Typing
module RUtil = Pulse.Reflection.Util

let rec gen_uvars (t_head:term) : T.Tac (list nat & comp) =
  let ropt = is_arrow t_head in
  match ropt with
  | Some (_, Some Implicit, c_rest) -> (
    let Tm_UVar n = gen_uvar () in
    let c_rest = open_comp_with c_rest (Tm_UVar n) in
    match c_rest with
    | C_ST c
    | C_STAtomic _ c
    | C_STGhost _ c ->
      [n], c_rest
    | C_Tot t ->
      let n_rest, comp_typ = gen_uvars t in
      n::n_rest, comp_typ
  )
  | _ ->
   T.fail (FStar.Printf.sprintf "gen_uvars: unexpected t_head: %s"
                                  (P.term_to_string t_head))

let rec check_valid_solution (n:nat) (t:term) (uv_sols:list (nat & term))
  : T.Tac (list (nat & term)) =

  match uv_sols with
  | [] -> [n, t]
  | (n', t')::tl ->
    if n = n'
    then if eq_tm t t' then uv_sols
         else T.fail "check_valid_solution failed"
    else (n', t')::(check_valid_solution n t tl)

let is_uvar (t:term) : bool =
  Some? (is_embedded_uvar t) || Tm_UVar? t

let uvar_index (t:term{is_uvar t}) : nat =
  match is_embedded_uvar t with
  | Some n -> n
  | _ ->
    match t with
    | Tm_UVar n -> n

let is_reveal_uvar (t:term) : option (universe & term & term) =
  match t with
  | Tm_PureApp (Tm_PureApp hd (Some Implicit) ty) None arg ->
    if is_uvar arg
    then match is_fvar hd with
         | Some (l, [u]) ->
           if l = RUtil.reveal_lid
           then Some (u, ty, arg)
           else None
         | _ -> None
    else None
  | _ -> None

let is_reveal (t:term) : bool =
  let hd, _ = leftmost_head_and_args t in
  match is_fvar hd with
  | Some (l, [_]) -> l = RUtil.reveal_lid
  | _ -> false

let rec match_typ (t1 t2:term) (uv_sols:list (nat & term))
  : T.Tac (list (nat & term)) =

  match is_reveal_uvar t1, is_reveal t2 with
  | Some (u, ty, t), false ->
    check_valid_solution (uvar_index t) (mk_hide u ty t2) uv_sols
  | _ ->
    if is_uvar t1
    then check_valid_solution (uvar_index t1) t2 uv_sols
    else match t1, t2 with
         | _, Tm_UVar _ -> T.fail "match_typ: t2 is a uvar"

         | Tm_PureApp head1 arg_qual1 arg1, Tm_PureApp head2 arg_qual2 arg2 ->
           if arg_qual1 = arg_qual2
           then let uv_sols = match_typ head1 head2 uv_sols in
                match_typ arg1 arg2 uv_sols
           else uv_sols

         | Tm_Pure t1, Tm_Pure t2 ->
           match_typ t1 t2 uv_sols
    
         | _, _ -> uv_sols

let rec atomic_vprop_has_uvar (t:term) : bool =
  if is_uvar t then true
  else match t with
       | Tm_PureApp head _ arg ->
         atomic_vprop_has_uvar head || atomic_vprop_has_uvar arg
       | Tm_Pure arg -> atomic_vprop_has_uvar arg
       | Tm_Emp -> false
       | _ -> false

let rec atomic_vprops_may_match (t1:term) (t2:term) : bool =
  if Some? (is_reveal_uvar t1) && not (is_reveal t2)
  then true
  else if is_uvar t1 then true
  else match t1, t2 with
       | Tm_PureApp head1 q1 arg1, Tm_PureApp head2 q2 arg2 ->
         atomic_vprops_may_match head1 head2 &&
         q1 = q2 &&
         atomic_vprops_may_match arg1 arg2
       | Tm_Pure x, Tm_Pure y ->
         atomic_vprops_may_match x y
       | _, _ -> eq_tm t1 t2

let infer_one_atomic_vprop (t:term) (ctxt:list term) (uv_sols:list (nat & term))
  : T.Tac (list (nat & term)) =

  if atomic_vprop_has_uvar t
  then
    let matching_ctxt = List.Tot.filter (fun ctxt_vp -> atomic_vprops_may_match t ctxt_vp) ctxt in
    T.print (FStar.Printf.sprintf "infer_one_atomic_vprop %s, found %d matching candidates\n"
               (P.term_to_string t)
               (List.Tot.length matching_ctxt));
    if List.Tot.length matching_ctxt = 1
    then
      let _ = T.print (FStar.Printf.sprintf "infer_one_atomic_vprop: matching %s and %s with %d exisiting solutions\n"
                         (P.term_to_string t)
                         (P.term_to_string (List.Tot.hd matching_ctxt))
                         (List.Tot.length uv_sols)) in 
      let uv_sols = match_typ t (List.Tot.hd matching_ctxt) uv_sols in
      T.print (FStar.Printf.sprintf "post matching, uv_sols has %d solutions\n"
                 (List.Tot.length uv_sols));
      uv_sols
    else uv_sols
  else uv_sols

let union_ranges (r0 r1:range) : T.Tac range = r0
let with_range (t:st_term') (r:range) : st_term = { term = t; range = r}

let rec rebuild_head (head:term) (uvs:list nat) (uv_sols:list (nat & term)) (r:range)
  : T.TacH st_term (requires fun _ -> List.Tot.length uvs > 0)
                   (ensures fun _ _ -> True) =
  let hd::tl = uvs in
  let ropt = List.Tot.find (fun (n1, _) -> hd = n1) uv_sols in
  match ropt with
  | None ->
    T.fail (FStar.Printf.sprintf
              "inference failed in building head, no solution for %d\n"
              hd)
  | Some (_, t2) ->
    match tl with
    | [] -> with_range (Tm_STApp { head; arg_qual= Some Implicit; arg=t2 })
                       r
    | _ ->
      let app_node = Tm_PureApp head (Some Implicit) t2 in
      rebuild_head app_node tl uv_sols r

let try_inst_uvs_in_goal (ctxt:term)
                         (goal:vprop)
  : T.Tac (list (nat & term))
  = let uv_sols = [] in
    let goal_list = vprop_as_list goal in
    let ctxt_list = vprop_as_list ctxt in
    let uv_sols =
      T.fold_left
        (fun uv_sols goal_vprop ->
          infer_one_atomic_vprop goal_vprop ctxt_list uv_sols)
        uv_sols
        goal_list
    in
    uv_sols

let print_solutions (l:list (nat & term))
  : T.Tac string
  = String.concat "\n"
      (T.map #(nat & term) #string
        (fun (u, t) ->
          Printf.sprintf "%d := %s" 
                       u
                       (P.term_to_string t))
        l)

let infer
  (head:term)
  (t_head:term)
  (ctxt_pre:term)
  (r:range)
  : T.Tac st_term =

  let uvs, pre =
    let uvs, comp = gen_uvars t_head in
    match comp with
    | C_ST st_comp
    | C_STAtomic _ st_comp
    | C_STGhost _ st_comp -> uvs, st_comp.pre
    | _ -> T.fail "infer:unexpected comp type"
  in

  if List.Tot.length uvs = 0
  then T.fail "Inference did not find anything to infer"
  else begin
    T.print (FStar.Printf.sprintf "infer: generated %d uvars,\n\
                                   ctx: {\n%s\n}\n\
                                   st_comp.pre:{\n%s\n}"
               (List.Tot.length uvs)
               (P.term_list_to_string "\n" (vprop_as_list ctxt_pre))
               (P.term_list_to_string "\n" (vprop_as_list pre)));

    let uv_sols = try_inst_uvs_in_goal ctxt_pre pre in
    T.print (Printf.sprintf "Got solutions: {\n%s\}"  (print_solutions uv_sols));
    let head = rebuild_head head uvs uv_sols r in
    T.print (Printf.sprintf "Rebuilt head= %s" (P.st_term_to_string head));
    head
  end

let find_solution (sol:list (nat * term)) (t:nat)
  : option term
  = let r = List.Tot.find (fun (u, _) -> u = t) sol in
    match r with
    | None -> None
    | Some (_, t) -> Some t
    
let rec apply_solution (sol:list (nat * term)) (t:term)
  : term
  = match t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> t

    | Tm_FStar _ _
    | Tm_UVar _ ->
      if is_uvar t
      then let n = uvar_index t in
            match find_solution sol n with
            | None -> t
            | Some t -> t
      else t
      
    | Tm_PureApp head q arg ->
      Tm_PureApp (apply_solution sol head)
                 q
                 (apply_solution sol arg)

    | Tm_Pure p ->
      Tm_Pure (apply_solution sol p)
    | Tm_Star l r ->
      Tm_Star (apply_solution sol l)
              (apply_solution sol r)
              
    | Tm_ExistsSL u t body se ->
      Tm_ExistsSL u (apply_solution sol t)
                    (apply_solution sol body)
                    se
       
    | Tm_ForallSL u t body ->
      Tm_ForallSL u (apply_solution sol t)
                    (apply_solution sol body)
                    
    // | Tm_FStar t r ->
    //   //TODO: What does inference mean for terms that contain embedded F* terms?
    //   Tm_FStar t r

// let apply_solution_binder (sol:list (term & term))
//                           (b:binder)
//   : binder
//   = { b with binder_ty = apply_solution sol b.binder_ty }

// let apply_solution_comp (sol:list (term & term))
//                         (c:comp)
//   : comp
//   = match c with
//     | C_Tot t ->
//       C_Tot (apply_solution sol t)
//     | _ -> c //TODO?


let rec contains_uvar (t:term)
  : bool
  = match t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> false
    | Tm_UVar _ -> true
      
    | Tm_PureApp head q arg ->
      contains_uvar head ||
      contains_uvar arg

    | Tm_Pure p ->
      (contains_uvar p)
      
    | Tm_Star l r ->
      (contains_uvar l) ||
      (contains_uvar r)
              
    | Tm_ExistsSL u t body se ->
      (contains_uvar t) ||
      (contains_uvar body)
       
    | Tm_ForallSL u t body ->
      (contains_uvar t) ||
      (contains_uvar body)
                    
    | Tm_FStar _ _ ->
      // TODO: should embedded F* terms be allowed to contain Pulse uvars?
      Some? (is_embedded_uvar t)

// let contains_uvar_binder  (b:binder)
//   : bool
//   = contains_uvar b.binder_ty

// let contains_uvar_comp  (c:comp)
//   : bool
//   = match c with
//     | C_Tot t ->
//       (contains_uvar t)
//     | _ -> true

let try_unify (l r:term) = match_typ l r []
