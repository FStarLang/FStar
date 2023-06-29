module Pulse.Checker.Abs

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV

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


#push-options "--z3rlimit_factor 2"
let check_abs
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  if Some? post_hint then fail g None "Unexpected post-condition annotation from context for an abstraction" else 
  let range = t.range in
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname}; q=qual; ascription=c; body } -> //pre=pre_hint; body; ret_ty; post=post_hint_body } ->
    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let (| t, _, _ |) = check_term g t in //elaborate it first
    let (| u, t_typing |) = check_universe g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let px = ppname, x in
    let var = tm_var {nm_ppname=ppname;nm_index=x} in
    let g' = push_binding g x ppname t in
    let pre_opened, ret_ty, post_hint_body = 
      match c with
      | C_Tot { t = Tm_Unknown } -> 
        tm_emp, None, None

      | C_Tot ty ->
        tm_emp,
        Some (open_term_nv ty px),
        None

      | _ -> 
        open_term_nv (comp_pre c) px,
        Some (open_term_nv (comp_res c) px),
        Some (open_term' (comp_post c) var 1)
    in
    let (| pre_opened, pre_typing |) = check_vprop g' pre_opened in
    let pre = close_term pre_opened x in
    let post =
      match post_hint_body with
      | None -> None
      | Some post ->
        let post_hint_typing
          : post_hint_t
          = Pulse.Checker.Common.intro_post_hint (push_context "post_hint_typing" range g') ret_ty post
        in
        Some post_hint_typing
    in
    let (| body', c_body, body_typing |) = check g' (open_st_term_nv body px) pre_opened pre_typing post in
    check_effect_annotation g' body'.range c c_body;
    FV.st_typing_freevars body_typing;
    let body_closed = close_st_term body' x in
    assume (open_st_term body_closed x == body');
    let b = {binder_ty=t;binder_ppname=ppname} in
    let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
    let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
    (| _, C_Tot tres, tt |)