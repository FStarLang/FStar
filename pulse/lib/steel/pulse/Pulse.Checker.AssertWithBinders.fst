module Pulse.Checker.AssertWithBinders

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Elaborate.Pure
open Pulse.Typing.Env
module L = FStar.List.Tot
module PC = Pulse.Checker.Pure
module P = Pulse.Syntax.Printer
module N = Pulse.Syntax.Naming 
module Inf = Pulse.Checker.Inference

let is_host_term (t:R.term) = not (R.Tv_Unknown? (R.inspect_ln t))
let infer_binder_types (g:env) (bs:list binder) (v:vprop) : T.Tac (list (binder & T.binder) & vprop) = 
    let tv = elab_term v in
    if not (is_host_term tv)
    then fail g (Some v.range) (Printf.sprintf "Cannot infer type of %s" (P.term_to_string v));
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
    let formals, body = 
        match inst_abstraction.t with
        | Tm_FStar t -> T.collect_abs t
        | _ -> T.fail "Impossible"
    in
    if not (is_host_term body)
    then T.fail "Impossible"
    else T.zip bs formals, tm_fstar body v.range

let instantiate_binders (bs:list (binder & T.binder)) (v:vprop)
  : T.Tac (list (Inf.uvar & term) & vprop)
  = let binder_uniq (x:T.binder) : nat = x.uniq in
    let uvs_subst = 
        T.map
            (fun (b,tb) -> 
                let uv, t = Inf.gen_uvar b.binder_ppname in
                (uv, t), N.NT (binder_uniq tb) t)
            bs
    in
    let uvs, subst = L.unzip uvs_subst in
    uvs, subst_term v subst

let check
  (g:env)
  (st:st_term{Tm_AssertWithBinders? st.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)
  = let Tm_AssertWithBinders { binders; v; t=body } = st.term in
    let t_binders, v = infer_binder_types g binders v in
    let uvs, v = instantiate_binders t_binders v in
    let solution = Pulse.Checker.Inference.try_inst_uvs_in_goal g pre v in
    match Inf.unsolved solution uvs with
    | Some uvs ->
      fail g (Some st.range) 
             (Printf.sprintf "Could not instantiate %s"
                             (String.concat ", " (T.map (fun (_, t) -> P.term_to_string t) uvs)))
    | _ ->
      let _, body_subst = 
        T.fold_right #_ #(nat & N.subst)
            (fun (uv, t) (index, subst) ->
                let sol = Inf.apply_solution solution t in 
                index + 1, N.DT index sol::subst)
            uvs
            (0, [])
      in
      let body = subst_st_term body body_subst in
      check g body pre pre_typing post_hint
    