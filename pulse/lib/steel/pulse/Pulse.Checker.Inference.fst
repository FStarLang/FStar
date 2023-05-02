module Pulse.Checker.Inference

module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Framing
module P = Pulse.Syntax.Printer

module RT = FStar.Reflection.Typing
module RUtil = Pulse.Reflection.Util

let rec gen_uvars (t_head:term) : T.Tac (list term & comp) =
  match t_head with
  | Tm_Arrow {binder_ty=t} (Some Implicit) c_rest -> (
    let uv = gen_uvar t in
    let c_rest = open_comp_with c_rest uv in
    match c_rest with
    | C_ST c
    | C_STAtomic _ c
    | C_STGhost _ c ->
      [uv], c_rest
    | C_Tot t ->
      let uv_rest, comp_typ = gen_uvars t in
      uv::uv_rest, comp_typ
  )
  | _ ->
   T.fail (FStar.Printf.sprintf "gen_uvars: unexpected t_head: %s"
                                  (P.term_to_string t_head))

let rec check_valid_solution (t1 t2:term) (uv_sols:list (term & term))
  : T.Tac (list (term & term)) =

  match uv_sols with
  | [] -> [t1, t2]
  | (t1', t2')::tl ->
    if eq_tm t1 t1'
    then if eq_tm t2 t2' then uv_sols
         else T.fail "check_valid_solution failed"
    else (t1', t2')::(check_valid_solution t1 t2 tl)

let is_reveal_uvar (t:term) : option (universe & term & term) =
  match t with
  | Tm_PureApp (Tm_PureApp (Tm_UInst l [u]) (Some Implicit) ty) None (Tm_UVar n) ->
    if l = RUtil.reveal_lid
    then Some (u, ty, Tm_UVar n)
    else None
  | _ -> None

let is_reveal (t:term) : bool =
  let hd, _ = leftmost_head_and_args t in
  match hd with
  | Tm_UInst l [_] -> l = RUtil.reveal_lid
  | _ -> false

let rec match_typ (t1 t2:term) (uv_sols:list (term & term))
  : T.Tac (list (term & term)) =

  match is_reveal_uvar t1, is_reveal t2 with
  | Some (u, ty, t), false ->
    check_valid_solution t (mk_hide u ty t2) uv_sols
  | _ ->
    match t1, t2 with
    | Tm_UVar n, _ ->
      check_valid_solution t1 t2 uv_sols
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
  match t with
  | Tm_UVar _ -> true
  | Tm_PureApp head _ arg ->
    atomic_vprop_has_uvar head || atomic_vprop_has_uvar arg
  | Tm_Pure arg -> atomic_vprop_has_uvar arg
  | Tm_Emp -> false
  | _ -> false

let rec atomic_vprops_may_match (t1:term) (t2:term) : bool =
  if Some? (is_reveal_uvar t1) && not (is_reveal t2)
  then true
  else match t1, t2 with
    | Tm_UVar _, _ -> true
    | Tm_PureApp head1 q1 arg1, Tm_PureApp head2 q2 arg2 ->
      atomic_vprops_may_match head1 head2 &&
      q1 = q2 &&
      atomic_vprops_may_match arg1 arg2
    | Tm_Pure x, Tm_Pure y ->
      atomic_vprops_may_match x y
    | _, _ -> eq_tm t1 t2

let infer_one_atomic_vprop (t:term) (ctxt:list term) (uv_sols:list (term & term))
  : T.Tac (list (term & term)) =

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
      let uv_sols = match_typ t (List.Tot.hd matching_ctxt) uv_sols in
      // T.print (FStar.Printf.sprintf "post matching, uv_sols has %d solutions\n"
      //            (List.Tot.length uv_sols));
      uv_sols
    else uv_sols
  else uv_sols

let rec rebuild_head (head:term) (uvs:list term) (uv_sols:list (term & term))
  : T.TacH st_term (requires fun _ -> List.Tot.length uvs > 0)
                   (ensures fun _ _ -> True) =
  let hd::tl = uvs in
  let ropt = List.Tot.find (fun (t1, _) -> eq_tm t1 hd) uv_sols in
  match ropt with
  | None -> T.fail "inference failed in building head"
  | Some (_, t2) ->
    match tl with
    | [] -> Tm_STApp head (Some Implicit) t2
    | _ ->
      let app_node = Tm_PureApp head (Some Implicit) t2 in
      rebuild_head app_node tl uv_sols

let try_inst_uvs_in_goal (ctxt:term)
                         (goal:vprop)
  : T.Tac (list (term & term))
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

let print_solutions (l:list (term * term)) 
  : T.Tac string
  = String.concat "\n"
      (T.map 
        (fun (u, t) ->
          Printf.sprintf "%s := %s" 
                       (P.term_to_string u)
                       (P.term_to_string t))
        l)

let infer
  (head:term)
  (t_head:term)
  (ctxt_pre:term)
  
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
    let head = rebuild_head head uvs uv_sols in
    T.print (Printf.sprintf "Rebuilt head= %s" (P.st_term_to_string head));
    head
  end

let find_solution (sol:list (term * term)) (uv:int)
  : option term
  = let r =
        List.Tot.find
          (fun (u, t) ->
            match u with
            | Tm_UVar u -> u = uv
            | _ -> false)
        sol
    in
    match r with
    | None -> None
    | Some (_, t) -> Some t
    
let rec apply_solution (sol:list (term * term)) (t:term)
  : term
  = match t with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Type _ 
    | Tm_Unknown -> t
    | Tm_UVar uv -> (
      match find_solution sol uv with
      | None -> t
      | Some t -> t
    )
      
    | Tm_Refine b t ->
      Tm_Refine (apply_solution_binder sol b)
                (apply_solution sol t)

    | Tm_PureApp head q arg ->
      Tm_PureApp (apply_solution sol head)
                 q
                 (apply_solution sol arg)

    | Tm_Let t e1 e2 ->
      Tm_Let (apply_solution sol t)
             (apply_solution sol e1)
             (apply_solution sol e2)

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
                    
    | Tm_Arrow b q body ->
      Tm_Arrow (apply_solution_binder sol b)
               q
               (apply_solution_comp sol body)

    | Tm_FStar t ->
      //TODO: What does inference mean for terms that contain embedded F* terms?
      Tm_FStar t

and apply_solution_binder (sol:list (term & term))
                          (b:binder)
  : binder
  = { b with binder_ty = apply_solution sol b.binder_ty }

and apply_solution_comp (sol:list (term & term))
                        (c:comp)
  : comp
  = match c with
    | C_Tot t ->
      C_Tot (apply_solution sol t)
    | _ -> c //TODO?


let rec contains_uvar (t:term)
  : bool
  = match t with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Type _ 
    | Tm_Unknown -> false
    | Tm_UVar _ -> true
      
    | Tm_Refine b t ->
      contains_uvar_binder b ||
      contains_uvar t

    | Tm_PureApp head q arg ->
      contains_uvar head ||
      contains_uvar arg

    | Tm_Let t e1 e2 ->
      (contains_uvar t) ||
      (contains_uvar e1) ||
      (contains_uvar e2)

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
                    
    | Tm_Arrow b q body ->
      (contains_uvar_binder b) ||
      (contains_uvar_comp body)

    | Tm_FStar t ->
      // TODO: should embedded F* terms be allowed to contain Pulse uvars?
      false

and contains_uvar_binder  (b:binder)
  : bool
  = contains_uvar b.binder_ty

and contains_uvar_comp  (c:comp)
  : bool
  = match c with
    | C_Tot t ->
      (contains_uvar t)
    | _ -> true

let try_unify (l r:term) = match_typ l r []
