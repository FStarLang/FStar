module Pulse.Checker.STApp

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module FV = Pulse.Typing.FV
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
module Prover = Pulse.Checker.Prover

let debug_log (g:env) (f:unit -> T.Tac unit) : T.Tac unit = if RU.debug_at_level (fstar_env g) "st_app" then f () else ()

let canon_comp (c:comp_st) : comp_st = 
  match readback_comp (elab_comp c) with
  | None -> c
  | Some (C_Tot _) -> c //should be impossible
  | Some c' ->
    c'
  
let canonicalize_st_typing (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  : st_typing g t (canon_comp c)
  = let c' = canon_comp c in
    let x = fresh g in
    assume ( ~(x `Set.mem` freevars (comp_post c)) /\
            ~(x `Set.mem` freevars (comp_post c')) );
    assume (st_equiv_pre c c');
    let st_eq 
      : st_equiv g c c'
      = ST_VPropEquiv g c c' x (magic()) (magic()) (magic()) (magic()) (magic())
    in
    T_Equiv _ _ _ _ d st_eq

let coerce_eq (#a #b:Type) (x:a) (_:squash (a === b)) : y:b { y == x } = x

let rec intro_uvars_for_logical_implicits (g:env) (uvs:env { disjoint uvs g }) (t:term) (ty:term)
  : T.Tac (uvs':env &
           g':env { extends_with g' g uvs' } &
           t':st_term { Tm_STApp? t'.term }) =
  
  let ropt = is_arrow ty in
  match ropt with
  | Some (b, Some Implicit, c_rest) ->
    let x = fresh (push_env g uvs) in
    let uvs' = push_binding uvs x ppname_default b.binder_ty in
    begin
      match c_rest with
       | C_ST _
       | C_STAtomic _ _
       | C_STGhost _ _ ->
         (| uvs', push_env g uvs', {term=Tm_STApp {head=t;arg_qual=Some Implicit;arg=null_var x};
                                    range=t.range} |)
       | C_Tot ty ->
         intro_uvars_for_logical_implicits g uvs' (tm_pureapp t (Some Implicit) (null_var x)) ty
    end
  | _ -> fail g None "intro_uvars_for_logical_implicits in stapp, unexpected type"

let instantaite_implicits (g:env) (t:st_term { Tm_STApp? t.term })
  : T.Tac (uvs : env &
           g' : env { extends_with g' g uvs } &
           t' : st_term { Tm_STApp? t'.term }) =

  let range = t.range in
  let Tm_STApp { head; arg_qual=qual; arg } = t.term in
  let pure_app = tm_pureapp head qual arg in
  let t, ty = instantiate_term_implicits g pure_app in
  match is_arrow ty with
  | Some (_, Some Implicit, _) ->
    //Some implicits to follow
    intro_uvars_for_logical_implicits g (mk_env (fstar_env g)) t ty
  | _ ->
    match is_pure_app t with
    | Some (head, q, arg) ->
      let uvs = mk_env (fstar_env g) in
      (| uvs, push_env g uvs, {term=Tm_STApp {head;arg_qual=q;arg}; range=t.range} |)
    | _ -> fail g None "instantiate_implicits in stapp, unexpected term"

#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let check
  (g0:env)
  (ctxt:vprop)
  (ctxt_typing:tot_typing g0 ctxt tm_vprop)
  (post_hint:post_hint_opt g0)
  (t:st_term { Tm_STApp? t.term })
  : T.Tac (checker_result_t g0 ctxt post_hint) =

  let g0 = push_context "st_app" t.range g0 in
  let range = t.range in

  let (| uvs, g, t |) = instantaite_implicits g0 t in

  let Tm_STApp { head; arg_qual=qual; arg } = t.term in
  let (| head, ty_head, dhead |) = check_term g head in
  debug_log g (fun _ ->
    T.print (Printf.sprintf "st_app: head = %s, ty_head = %s\n"
               (P.term_to_string head)
               (P.term_to_string ty_head)));
    
  match is_arrow ty_head with
  | Some ({binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ) ->
    is_arrow_tm_arrow ty_head;
    debug_log g (fun _ ->
      T.print (Printf.sprintf "st_app, readback comp as %s\n"
                 (P.comp_to_string comp_typ)));
    
    assert (ty_head ==
            tm_arrow ({binder_ty=formal;binder_ppname=ppname}) bqual comp_typ);
    
    if qual = bqual
    then
      let (| arg, darg |) = check_term_with_expected_type g arg formal in
      match comp_typ with
      | C_ST res
      | C_STAtomic _ res
      | C_STGhost _ res ->
        // This is a real ST application
        let d : st_typing _ _ (open_comp_with comp_typ arg) =
          T_STApp g head formal qual comp_typ arg (E dhead) (E darg) in
        let d = canonicalize_st_typing d in
        let t = wr (Tm_STApp {head; arg_qual=qual; arg}) in
        let c = (canon_comp (open_comp_with comp_typ arg)) in
        let d : st_typing g t c = d in

        Prover.repack (Prover.try_frame_pre_uvs ctxt_typing uvs d) post_hint t.range
      | _ ->
        fail g (Some t.range) "Expected an effectful application; got a pure term (could it be partially applied by mistake?)"
    else fail g (Some t.range) (Printf.sprintf "Unexpected qualifier in head type %s of stateful application: head = %s, arg = %s"
                (P.term_to_string ty_head)
                (P.term_to_string head)
                (P.term_to_string arg))

  | _ -> fail g (Some t.range) (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head))
#pop-options
