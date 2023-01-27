module Pulse.Checker.Inference

module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Framing
module P = Pulse.Syntax.Printer

module RT = Refl.Typing

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

let rec match_typ (t1 t2:term) (uv_sols:list (term & term))
  : T.Tac (list (term & term)) =

  match t1, t2 with
  | Tm_UVar n, _ ->
    check_valid_solution t1 t2 uv_sols
  | _, Tm_UVar _ -> T.fail "match_typ: t2 is a uvar"

  | Tm_PureApp head1 arg_qual1 arg1, Tm_PureApp head2 arg_qual2 arg2 ->
    if arg_qual1 = arg_qual2
    then let uv_sols = match_typ head1 head2 uv_sols in
         match_typ arg1 arg2 uv_sols
    else uv_sols

  | _, _ -> uv_sols

let rec atomic_vprop_has_uvar (t:term) : bool =
  match t with
  | Tm_UVar _ -> true
  | Tm_PureApp head _ arg ->
    atomic_vprop_has_uvar head || atomic_vprop_has_uvar arg
  | Tm_Emp -> false
  | _ -> false

let rec atomic_vprops_may_match (t1:term) (t2:pure_term) : bool =
  match t1, t2 with
  | Tm_UVar _, _ -> true
  | Tm_PureApp head1 q1 arg1, Tm_PureApp head2 q2 arg2 ->
    atomic_vprops_may_match head1 head2 &&
    q1 = q2 &&
    atomic_vprops_may_match arg1 arg2
  | _, _ -> eq_tm t1 t2

let infer_one_atomic_vprop (t:pure_term) (ctxt:list pure_term) (uv_sols:list (term & term))
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
  : T.Tac term
  = match uvs with
    | [] -> head
    | hd::tl ->
      let ropt = List.Tot.find (fun (t1, _) -> eq_tm t1 hd) uv_sols in
      match ropt with
      | None -> T.fail "inference failed in building head"
      | Some (_, t2) ->
        match tl with
        | [] -> Tm_STApp head (Some Implicit) t2
        | _ ->
          let app_node = Tm_PureApp head (Some Implicit) t2 in
          rebuild_head app_node tl uv_sols

let infer
  (head:term)
  (t_head:term)
  (ctxt_pre:term)
  
  : T.Tac term =

  let uvs, pre =
    let uvs, comp = gen_uvars t_head in
    match comp with
    | C_ST st_comp
    | C_STAtomic _ st_comp
    | C_STGhost _ st_comp -> uvs, st_comp.pre
    | _ -> T.fail "infer:unexpected comp type"
  in

  if List.Tot.length uvs = 0
  then head
  else begin
    // T.print (FStar.Printf.sprintf "infer: generated %d uvars, ctx: %s, st_comp.pre: %s\n"
    //            (List.Tot.length uvs)
    //            (P.term_to_string ctxt_pre)
    //            (P.term_to_string pre));

    let uv_sols = [] in
    
    assume (is_pure_term pre);
    let pre_list = vprop_as_list pre in

    assume (is_pure_term ctxt_pre);
    let ctxt_pre_list = vprop_as_list ctxt_pre in

    let uv_sols = T.fold_left (fun uv_sols st_pre_vprop ->
      infer_one_atomic_vprop st_pre_vprop ctxt_pre_list uv_sols) uv_sols pre_list in

    let head = rebuild_head head uvs uv_sols in
    head
  end
