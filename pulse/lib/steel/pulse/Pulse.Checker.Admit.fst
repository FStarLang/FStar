module Pulse.Checker.Admit

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module P = Pulse.Syntax.Printer

let post_hint_compatible (p:option post_hint_t) (x:var) (t:term) (u:universe) (post:vprop) =
  match p with
  | None -> True
  | Some p ->
    p.post== close_term post x /\
    p.u == u /\
    p.ret_ty == t

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (t:st_term { Tm_Admit? t.term })

  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_admit" t.range in

  let Tm_Admit { ctag = c; typ=t; post } = t.term in

  let x = fresh g in
  let px = v_as_nv x in
  let res
    : (t:term &
       u:universe &
       universe_of g t u &
       post:vprop { post_hint_compatible post_hint x t u post } &
       tot_typing (push_binding g x (fst px) t) post tm_vprop)
    = match post, post_hint with
      | None, None ->
        fail g None "could not find a post annotation on admit, please add one"

      | Some post1, Some post2 ->
        fail g None
          (Printf.sprintf "found two post annotations on admit: %s and %s, please remove one"
             (P.term_to_string post1)
             (P.term_to_string post2.post))
      
      | Some post, _ ->
        let (| u, t_typing |) = check_universe g t in    
        let post_opened = open_term_nv post px in      
        let (| post, post_typing |) = 
            check_term_with_expected_type (push_binding g x (fst px) t) post_opened tm_vprop
        in
        (| t, u, t_typing, post, E post_typing |)

      | _, Some post ->
        let post : post_hint_t = post in
        if x `Set.mem` freevars post.post
        then fail g None "Impossible: unexpected freevar clash in Tm_Admit, please file a bug-report"
        else (
          let post_typing_rec = post_hint_typing g post x in
          let post_opened = open_term_nv post.post px in              
          assume (close_term post_opened x == post.post);
          (| post.ret_ty, post.u, post_typing_rec.ty_typing, post_opened, post_typing_rec.post_typing |)
        )
  in
  let (| t, u, t_typing, post_opened, post_typing |) = res in
  let post = close_term post_opened x in
  let s : st_comp = {u;res=t;pre;post} in

  assume (open_term (close_term post_opened x) x == post_opened);
  let d = T_Admit _ _ c (STC _ s x t_typing pre_typing post_typing) in
  prove_post_hint (try_frame_pre pre_typing d) post_hint t.range
