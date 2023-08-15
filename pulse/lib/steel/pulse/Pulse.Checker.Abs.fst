module Pulse.Checker.Abs

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
(* Infers the the type of the binders from the specification alone, not the body *)

let rec arrow_of_abs (t:st_term { Tm_Abs? t.term })
  : T.Tac term
  = let Tm_Abs { b; q; ascription; body } = t.term in
    if Tm_Abs? body.term
    then (
      let arr = arrow_of_abs body in
      tm_arrow b q (C_Tot arr)
    )
    else
      tm_arrow b q ascription
module Env = Pulse.Typing.Env

let rec rebuild_abs (g:env) (t:st_term) (annot:T.term)
  : T.Tac (t:st_term { Tm_Abs? t.term })
  = match t.term, R.inspect_ln annot with
    | Tm_Abs { b; q; ascription=C_Tot un; body }, R.Tv_Arrow b' c' -> (
      let ty = readback_ty (T.inspect_binder b').sort in
      let comp = R.inspect_comp c' in
      match ty, comp with
      | Some ty, T.C_Total res_ty ->
        let b = { binder_ty = ty ; binder_ppname = b.binder_ppname } in
        let body = rebuild_abs g body res_ty in
        { t with term = Tm_Abs { b; q; ascription=C_Tot un; body }}
      | _ ->
        Env.fail g (Some t.range) 
            (Printf.sprintf "Unexpected type of abstraction: %s"
                (T.term_to_string annot))
    )
    | Tm_Abs { b; q; ascription=_; body }, R.Tv_Arrow b' c' -> (
      let ty = readback_ty (T.inspect_binder b').sort in
      let comp = R.inspect_comp c' in
      match ty, comp with
      | Some ty, R.C_Total res -> (
        let c = readback_comp res in
        match c with
        | None -> 
          Env.fail g (Some t.range) 
                      (Printf.sprintf "Unexpected computation type in abstraction: %s"
                          (T.term_to_string res))
        | Some c ->
          let b = { binder_ty = ty ; binder_ppname = b.binder_ppname } in
          { t with term = Tm_Abs { b; q; ascription=c; body }}
      )
      | _ ->
        Env.fail g (Some t.range) 
                    (Printf.sprintf "Unexpected type of abstraction: %s"
                          (T.term_to_string annot))
    )
    | _ -> 
      Env.fail g (Some t.range) 
                (Printf.sprintf "Unexpected arity of abstraction: expected a term of type %s"
                      (T.term_to_string annot))

let preprocess_abs
      (g:env)
      (t:st_term{Tm_Abs? t.term})
  : T.Tac (t:st_term { Tm_Abs? t.term })
  = let annot = arrow_of_abs t in
    let annot, _ = Pulse.Checker.Pure.instantiate_term_implicits g annot in
    match annot.t with
    | Tm_FStar annot ->
      rebuild_abs g t annot
    | _ ->
      Env.fail g (Some t.range) 
                 (Printf.sprintf "Expected an arrow type as an annotation, got %s"
                          (P.term_to_string annot))

let check_effect_annotation g r (c_annot c_computed:comp) =
  match c_annot, c_computed with
  | C_Tot _, C_Tot _ -> ()
  | C_ST _, C_ST _ -> ()
  | C_STAtomic i _, C_STAtomic j _
  | C_STGhost i _, C_STGhost j _ ->
    if eq_tm i j
    then ()
    else fail g (Some i.range)
                (Printf.sprintf "Annotated effect expects only invariants in %s to be opened; but computed effect claims that invariants %s are opened"
                  (P.term_to_string i)
                  (P.term_to_string j))
  | _, _ ->
    fail g (Some r)
           (Printf.sprintf "Expected effect %s but this function body has effect %s"
                  (P.tag_of_comp c_annot)
                  (P.tag_of_comp c_computed))


#push-options "--z3rlimit_factor 2 --fuel 0 --ifuel 1"
let rec check_abs_core
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let range = t.range in
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname}; q=qual; ascription=c; body } -> //pre=pre_hint; body; ret_ty; post=post_hint_body } ->

    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let (| t, _, _ |) = check_tot_term g t in //elaborate it first
    let (| u, t_typing |) = check_universe g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let px = ppname, x in
    let var = tm_var {nm_ppname=ppname;nm_index=x} in
    let g' = push_binding g x ppname t in
    let body_opened = open_st_term_nv body px in
    match body_opened.term with
    | Tm_Abs _ ->
      let (| body, c_body, body_typing |) = check_abs_core g' body_opened check in
      check_effect_annotation g' body.range c c_body;
      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| _, C_Tot tres, tt |)
    | _ ->
      let pre_opened, ret_ty, post_hint_body = 
        match c with
        | C_Tot _ ->
          fail g (Some body.range)
            "Unexpected error: found a total computation annotation on a top-level function" 

        | _ -> 
          open_term_nv (comp_pre c) px,
          Some (open_term_nv (comp_res c) px),
          Some (open_term' (comp_post c) var 1)
      in
      let (| pre_opened, pre_typing |) = check_vprop g' pre_opened in
      let pre = close_term pre_opened x in
      let post : post_hint_opt g' =
        match post_hint_body with
        | None -> fail g (Some body.range) "Top-level functions must be annotated with pre and post conditions"
        | Some post ->
          let post_hint_typing
            : post_hint_t
            = Pulse.Checker.Base.intro_post_hint (push_context "post_hint_typing" range g') (Some (ctag_of_comp_st c)) ret_ty post
          in
          Some post_hint_typing
      in

      let ppname = mk_ppname_no_range "_fret" in
      let r  = check g' pre_opened pre_typing post ppname body_opened  in
      let (| body, c_body, body_typing |) : st_typing_in_ctxt g' pre_opened post =
        apply_checker_result_k #_ #_ #(Some?.v post) r ppname in

      check_effect_annotation g' body.range c c_body;

      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| _, C_Tot tres, tt |)

let check_abs (g:env) (t:st_term{Tm_Abs? t.term}) (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let t = preprocess_abs g t in
  check_abs_core g t check