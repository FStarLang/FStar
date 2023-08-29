module Pulse.Checker.AssertWithBinders


open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Elaborate.Pure
open Pulse.Typing.Env

module L = FStar.List.Tot
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module PC = Pulse.Checker.Pure
module P = Pulse.Syntax.Printer
module N = Pulse.Syntax.Naming
module PS = Pulse.Checker.Prover.Substs
module Prover = Pulse.Checker.Prover

module RU = Pulse.RuntimeUtils

let is_host_term (t:R.term) = not (R.Tv_Unknown? (R.inspect_ln t))

let debug_log = Pulse.Typing.debug_log "with_binders"

let option_must (f:option 'a) (msg:string) : T.Tac 'a =
  match f with
  | Some x -> x
  | None -> T.fail msg

let rec refl_abs_binders (t:R.term) (acc:list binder) : T.Tac (list binder) =
  let open R in
  match inspect_ln t with
  | Tv_Abs b body ->
    let {sort; ppname} = R.inspect_binder b in
    let sort = option_must (readback_ty sort)
      (Printf.sprintf "Failed to readback elaborated binder sort %s in refl_abs_binders"
         (T.term_to_string sort)) in
    refl_abs_binders body
     ({ binder_ty = sort; binder_ppname = mk_ppname ppname (RU.range_of_term t) }::acc)
  | _ -> L.rev acc  

let infer_binder_types (g:env) (bs:list binder) (v:vprop)
  : T.Tac (list binder) =
  match bs with
  | [] -> []
  | _ ->
    let tv = elab_term v in
    if not (is_host_term tv)
    then fail g (Some v.range)
           (Printf.sprintf "assert.infer_binder_types: elaborated %s to %s, which failed the host term check"
              (P.term_to_string v) (T.term_to_string tv));
    let as_binder (b:binder) : R.binder =
      let open R in
      let bv : binder_view = 
        { sort = elab_term b.binder_ty;
          ppname = b.binder_ppname.name;
          qual = Q_Explicit;
          attrs = [] } in
      pack_binder bv
    in
    let abstraction = 
      L.fold_right 
        (fun b (tv:host_term) -> 
         let b = as_binder b in
         R.pack_ln (R.Tv_Abs b tv))
        bs
        tv
    in
    let inst_abstraction, _ = PC.instantiate_term_implicits g (tm_fstar abstraction v.range) in
    match inst_abstraction.t with
    | Tm_FStar t -> refl_abs_binders t []
    | _ -> T.fail "Impossible: instantiated abstraction is not embedded F* term, please file a bug-report"

let rec open_binders (g:env) (bs:list binder) (uvs:env { disjoint uvs g }) (v:term) (body:st_term)
  : T.Tac (uvs:env { disjoint uvs g } & term & st_term) =

  match bs with
  | [] -> (| uvs, v, body |)
  | b::bs ->
    // these binders are only lax checked so far
    let _ = PC.check_universe (push_env g uvs) b.binder_ty in
    let x = fresh (push_env g uvs) in
    let ss = [ DT 0 (tm_var {nm_index=x;nm_ppname=b.binder_ppname}) ] in
    let bs = L.mapi (fun i b ->
      assume (i >= 0);
      subst_binder b (shift_subst_n i ss)) bs in
    let v = subst_term v (shift_subst_n (L.length bs) ss) in
    let body = subst_st_term body (shift_subst_n (L.length bs) ss) in
    open_binders g bs (push_binding uvs x b.binder_ppname b.binder_ty) v body

let close_binders (bs:list (var & typ)) (t:term) : term =
  let r = L.fold_right (fun (x, _) (n, t) ->
    let ss = [ ND x 0 ] in
    n + 1,
    subst_term t (shift_subst_n n ss)
  ) bs (0, t) in
  snd r

let unfold_defs (g:env) (defs:option (list string)) (t:term) 
  : T.Tac term
  = let t = elab_term t in
    let head, _ = T.collect_app t in
    match R.inspect_ln head with
    | R.Tv_FVar fv
    | R.Tv_UInst fv _ -> (
        let head = String.concat "." (R.inspect_fv fv) in
        let fully = 
          match defs with
          | Some defs -> defs
          | None -> []
        in
        let rt = RU.unfold_def (fstar_env g) head fully t in
        let rt = option_must rt
          (Printf.sprintf "unfolding %s returned None" (T.term_to_string t)) in
        let ty = option_must (readback_ty rt)
          (Printf.sprintf "error in reading back the unfolded term %s" (T.term_to_string rt)) in
        debug_log g (fun _ -> Printf.sprintf "Unfolded %s to F* term %s and readback as %s" (T.term_to_string t) (T.term_to_string rt) (P.term_to_string ty));
        ty
      )
    | _ ->
      fail g (Some (RU.range_of_term t))
        (Printf.sprintf "Cannot unfold %s, the head is not an fvar" (T.term_to_string t))

let check_unfoldable g (v:term) : T.Tac unit = 
  match v.t with
  | Tm_FStar _ -> ()
  | _ -> 
   fail g 
      (Some v.range)
      (Printf.sprintf "`fold` and `unfold` expect a single user-defined predicate as an argument, \
                        but %s is a primitive term that cannot be folded or unfolded"
                        (P.term_to_string v))

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_ProofHintWithBinders? st.term })
  (check:check_t)

  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context g "check_assert" st.range in

  let Tm_ProofHintWithBinders { hint_type; binders=bs; t=body } = st.term in

  match hint_type with
  | RENAME _ ->
    T.fail "Renaming not yet handled"
    
  | ASSERT { p = v } ->
    let bs = infer_binder_types g bs v in
    let (| uvs, v_opened, body_opened |) = open_binders g bs (mk_env (fstar_env g)) v body in
    let v, body = v_opened, body_opened in
    let (| v, d |) = PC.check_vprop (push_env g uvs) v in
    let (| g1, nts, pre', k_frame |) = Prover.prove pre_typing uvs d in
    let (| x, x_ty, pre'', g2, k |) =
      check g1 (tm_star (PS.nt_subst_term v nts) pre') (magic ()) post_hint res_ppname (PS.nt_subst_st_term body nts) in
    (| x, x_ty, pre'', g2, k_elab_trans k_frame k |)


  | UNFOLD { names; p=v }
  | FOLD { names; p=v } ->
    let bs = infer_binder_types g bs v in
    let (| uvs, v_opened, body_opened |) = open_binders g bs (mk_env (fstar_env g)) v body in
    check_unfoldable g v;
    let v_opened, _ = PC.instantiate_term_implicits (push_env g uvs) v_opened in
    let lhs, rhs =
      match hint_type with      
      | UNFOLD _ ->
        v_opened,
        unfold_defs (push_env g uvs) None v_opened
      | FOLD { names=ns } -> 
        unfold_defs (push_env g uvs) ns v_opened,
        v_opened in
    let uvs_bs = L.rev (bindings uvs) in
    let lhs, rhs = close_binders uvs_bs lhs, close_binders uvs_bs rhs in
    let rw = { term = Tm_Rewrite { t1 = lhs;
                                   t2 = rhs };
               range = st.range } in
    let st = { term = Tm_Bind { binder = as_binder (tm_fstar (`unit) st.range);
                                head = rw; body };
               range = st.range } in

    let st =
      match bs with
      | [] -> st
      | _ ->
        { term = Tm_ProofHintWithBinders { hint_type = ASSERT { p = lhs };
                                           binders = bs;
                                           t = st };
          range = st.range } in
    check g pre pre_typing post_hint res_ppname st
