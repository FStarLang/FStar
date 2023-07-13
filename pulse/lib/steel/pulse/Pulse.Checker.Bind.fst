module Pulse.Checker.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Common
open Pulse.Checker.Pure
module FV = Pulse.Typing.FV
module LN = Pulse.Typing.LN
module Metatheory = Pulse.Typing.Metatheory

#push-options "--query_stats --ifuel 2 --z3rlimit_factor 4"
let  mk_bind'
  (g:env)
  (pre:term)
  (e1:st_term)
  (e2:st_term)
  (c1:comp_st)
  (c2:comp_st)
  (px:nvar { ~ (Set.mem (snd px) (dom g)) })
  (d_e1:st_typing g e1 c1)
  (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1)))
  (d_e2:st_typing (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2)
  (post_hint:post_hint_opt g { comp_post_matches_hint c2 post_hint })
  (_:squash (let _, x = px in
             comp_pre c1 == pre /\
             None? (lookup g x) /\
             (~(x `Set.mem` freevars_st e2)) /\
             open_term (comp_post c1) x == comp_pre c2))
  : T.Tac (checker_result_t g pre post_hint true)
   = let _,x  = px in
     let s2 = st_comp_of_comp c2 in
     if x `Set.mem` freevars s2.post
     then fail g None (Printf.sprintf "Bound variable %d escapes scope in postcondition %s" x (P.term_to_string s2.post))
     else ( 
       let res_typing, post_typing = bind_res_and_post_typing g s2 x post_hint  in
       let (| t, c, d |) = mk_bind g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing in
       (| t, c, d |)
     )

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let check_bind
  (g:env)
  (t:st_term{Tm_Bind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (frame_pre:bool)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint frame_pre) =
  if not frame_pre
  then T.fail "check_bind: frame_pre is false, bailing";
  let Tm_Bind { binder=b; head=e1; body=e2 } = t.term in
  let (| e1, c1, d1 |) = check g e1 pre pre_typing None frame_pre in
  if not (stateful_comp c1)
  then fail g None "Bind: c1 is not st"
  else 
    let s1 = st_comp_of_comp c1 in
    let t = s1.res in
    let (| t_typing, _, x, next_pre_typing |) = 
      Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness d1))) in
    let px = b.binder_ppname, x in
    let next_pre = open_term_nv s1.post px in
    let g' = push_binding g x b.binder_ppname s1.res in
    let (| e2', c2, d2 |) = check g' (open_st_term_nv e2 px) next_pre next_pre_typing post_hint frame_pre in
    FV.st_typing_freevars d2;
    if not (stateful_comp c2)
    then fail g None "Bind: c2 is not st"
    else ( 
      let e2_closed = close_st_term e2' x in
      assume (open_st_term e2_closed x == e2');
      mk_bind' g pre e1 e2_closed c1 c2 px d1 t_typing d2 post_hint ()
    )
//inlining mk_bind' causes memory to blow up. F* takes a long time to compute a VC for the definition above^. Z3 finishes the proof quickly    
#pop-options

let check_tot_bind g t pre pre_typing post_hint frame_pre check =
  if not frame_pre
  then T.fail "check_tot_bind: frame_pre is false, bailing";
  let Tm_TotBind { head=e1; body=e2 } = t.term in
  let (| e1, u1, t1, _t1_typing, e1_typing |) = check_term_and_type g e1 in
  let t1 =
    let b = {binder_ty=t1;binder_ppname=ppname_default} in
    let eq_tm = mk_eq2 u1 t1 (null_bvar 0) e1 in
    tm_refine b eq_tm in
  let (| e1, e1_typing |) =
    check_term_with_expected_type g e1 t1 in
  let x = fresh g in
  let px = v_as_nv x in
  let g' = push_binding g x (fst px) t1 in
  // This is just weakening,
  //   we have g |- pre : vprop
  //   g' should follow by some weakening lemma
  let pre_typing' : tot_typing g' pre tm_vprop =
    check_vprop_with_core g' pre in
  let (| e2, c2, e2_typing |) =
    check g' (open_st_term_nv e2 px) pre pre_typing' post_hint frame_pre in
  if not (stateful_comp c2)
  then fail g (Some e2.range) "Tm_TotBind: e2 is not a stateful computation"
  else
    let e2_closed = close_st_term e2 x in
    assume (open_st_term_nv e2_closed (v_as_nv x) == e2);
    assert (comp_pre c2 == pre);
    // T.print (Printf.sprintf "c2 is %s\n\n" (P.comp_to_string c2));
    FV.tot_typing_freevars pre_typing;
    close_with_non_freevar pre x 0;
    let c = open_comp_with (close_comp c2 x) e1 in
    let _ = 
      match post_hint with
      | None -> ()
      | Some post ->
        assume (comp_post c == comp_post c2 /\
                comp_res c == comp_res c2 /\
                comp_u c == comp_u c2)
    in
    // T.print (Printf.sprintf "c is %s\n\n" (P.comp_to_string c));
    LN.tot_typing_ln pre_typing';
    open_with_gt_ln pre (-1) e1 0;
    (| _,
       c,
       T_TotBind _ _ e2_closed _ _ x (E e1_typing) e2_typing |)

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

// let check_stapp_no_ctxt (g:env) (t:st_term { Tm_STApp? t.term })
//   : T.Tac (uvs : env { disjoint uvs g } &
//            t:st_term &
//            c:comp_st &
//            st_typing (push_env g uvs) t c) = magic ()

module PS = Pulse.Prover.Substs
open Pulse.Prover.Common
open Pulse.Prover
#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let check_bindv2
  (g:env)
  (t:st_term {Tm_Bind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (frame_pre:bool)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint frame_pre) =

  if not frame_pre
  then T.fail "check_bindv2: frame_pre is not set, bailing";

  let Tm_Bind { binder=b; head=e1; body=e2 } = t.term in

  match e1.term with
  | _ ->
    // let (| uvs, e1, c1, d1 |) =
    let (| e1, c1, d1 |) =
      check g e1 pre pre_typing None false in
    let uvs = mk_env (fstar_env g) in
      // check_stapp_no_ctxt g e1 in
    let c10 = c1 in
    // magic is comp_pre c1 typing, get from inversion of d1
    assume (stateful_comp c1);
    let (| g1, uvs1, ss1, remaining_pre, k |) =
      prove pre_typing uvs #(comp_pre c1) (magic ()) in
    let x = fresh g1 in
    let px = b.binder_ppname, x in
    // TODO: if the binder is annotated, check subtyping
    let g2 = push_binding g1 x b.binder_ppname (PS.nt_subst_term (comp_res c1) ss1) in
    let pre_e2 = open_term_nv (PS.nt_subst_term (comp_post c1) ss1) px * remaining_pre in
    assert (g2 `env_extends` g1);
    assert (g2 `env_extends` g);
    // magic is the typing of pre_e2 in g2
    // remaining_pre is well-typed, may be prove function can return it?
    // well-typedness of open_term?
    let (| e2, c2, d2 |) =
      check g2 (open_st_term_nv e2 px) pre_e2 (magic ()) (extend_post_hint_opt_g g post_hint g2) frame_pre in
    
    if not (stateful_comp c2)
    then fail g None "Bind: c2 is not st"
    else
      let _ = assert (equal g (push_env g uvs)) in
      let d1 = st_typing_weakening g uvs e1 c1 d1 g1 in
      let d1 = st_typing_weakening_end g1 uvs e1 c1 d1 uvs1 in
      let d1 = PS.st_typing_nt_substs_derived g1 uvs1 #e1 #c1 d1 ss1 in
      let (| e1, c1, d1 |) = add_frame d1 #remaining_pre (magic ()) in
      assert (comp_pre c1 == PS.nt_subst_term (comp_pre c10) ss1 * remaining_pre);
      assert (comp_res c1 == PS.nt_subst_term (comp_res c10) ss1);
      assert (None? (lookup g1 x));
      assert (comp_post c1 == PS.nt_subst_term (comp_post c10) ss1 * remaining_pre);
      assume (open_term remaining_pre x == remaining_pre);
      assert (open_term (comp_post c1) x == comp_pre c2);
   
      let e2_closed = close_st_term e2 x in
      assume (open_st_term e2_closed x == e2);
      let r = mk_bind' g1 (comp_pre c1) e1 e2_closed c1 c2 px (coerce_eq d1 ()) (magic ()) (coerce_eq d2 ()) post_hint () in

      k post_hint r
  | _ -> fail g None "Bind: e1 is not an stapp"
#pop-options
