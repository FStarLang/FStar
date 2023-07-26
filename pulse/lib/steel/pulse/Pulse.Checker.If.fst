module Pulse.Checker.If

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory

#push-options "--z3rlimit_factor 10 --fuel 0 --ifuel 1"
let rec combine_if_branches
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : T.TacH (c:comp_st{st_comp_of_comp c == st_comp_of_comp c_then} &
            st_typing g_then e_then c &
            st_typing g_else e_else c)
           (requires fun _ ->
              comp_pre c_then == comp_pre c_else)
           (ensures fun _ _ -> True) =
  let g = g_then in
  if eq_st_comp (st_comp_of_comp c_then) (st_comp_of_comp c_else)
  then begin
    match c_then, c_else with
    | C_ST _, C_ST _ -> (| c_then, e_then_typing, e_else_typing |)
    | C_STAtomic inames1 _, C_STAtomic inames2 _
    | C_STGhost inames1 _, C_STGhost inames2 _ ->
      if eq_tm inames1 inames2
      then (| c_then, e_then_typing, e_else_typing |)
      else fail g None
             (Printf.sprintf "Cannot combine then and else branches (different inames %s and %s)"
                (P.term_to_string inames1)
                (P.term_to_string inames2))
    | C_ST _, C_STAtomic inames _ ->
      if eq_tm inames tm_emp_inames
      then begin
        let e_else_typing =
          T_Lift g_else e_else c_else c_then e_else_typing
            (Lift_STAtomic_ST g_else c_else) in
        (| c_then, e_then_typing, e_else_typing |)
      end
      else fail g None
             (Printf.sprintf "Cannot lift STAtomic else branch to match ST then branch, inames %s not empty"
                (P.term_to_string inames))
    | C_STAtomic inames _, C_ST _ ->
      if eq_tm inames tm_emp_inames
      then begin
        let e_then_typing =
          T_Lift g_then e_then c_then c_else e_then_typing
            (Lift_STAtomic_ST g_then c_then) in
        (| c_else, e_then_typing, e_else_typing |)
      end
      else fail g None
             (Printf.sprintf "Cannot lift STAtomic then branch to match ST else branch, inames %s not empty"
                (P.term_to_string inames))
    | C_STGhost _ _, _ ->
      let w = get_non_informative_witness g_then (comp_u c_then) (comp_res c_then) in
      let e_then_typing =
        T_Lift _ _ _ _ e_then_typing (Lift_STGhost_STAtomic _ _ w) in
      let (| c, e1_typing, e2_typing |) =
        combine_if_branches _ _ _ e_then_typing _ _ _ e_else_typing in
      (| c, e1_typing, e2_typing |)
    | _, C_STGhost _ _ ->
      let w = get_non_informative_witness g_else (comp_u c_else) (comp_res c_else) in
      let e_else_typing =
        T_Lift _ _ _ _ e_else_typing (Lift_STGhost_STAtomic _ _ w) in
      combine_if_branches _ _ _ e_then_typing _ _ _ e_else_typing
    | _, _ ->
      fail g None
         (Printf.sprintf "Cannot combine then and else branches (incompatible effects %s and %s resp.)"
            (P.ctag_to_string (ctag_of_comp_st c_then))
            (P.ctag_to_string (ctag_of_comp_st c_else)))
  end
  else fail g None "Cannot combine then and else branches (different st_comp)"
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let check
  (g:env)
  (pre:term)
  (pre_typing: tot_typing g pre tm_vprop)
  (post_hint:post_hint_for_env g)
  (res_ppname:ppname)
  (b:term)
  (e1 e2:st_term)
  (check:check_t)
  : T.Tac (checker_result_t g pre (Some post_hint)) =
  
  let g = Pulse.Typing.Env.push_context g "check_if" e1.range in

  let (| b, b_typing |) =
    check_term_with_expected_type g b tm_bool in

  let post = post_hint.post in
  let hyp = fresh g in
  let g_with_eq (eq_v:term) =
    push_binding g hyp (mk_ppname_no_range "_if_hyp") (mk_eq2 u0 tm_bool b eq_v)
  in

  let check_branch (eq_v:term) (br:st_term) (is_then:bool)
    : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
             c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (Some post_hint)} &
             st_typing (g_with_eq eq_v) br c) =
    let g_with_eq = g_with_eq eq_v in
    let pre_typing = 
      Metatheory.tot_typing_weakening_single
        pre_typing
        hyp 
        (mk_eq2 u0 tm_bool b eq_v)
    in
    let r = check g_with_eq pre pre_typing (Some post_hint) (mk_ppname_no_range "_if_br") br in
    let (| br, c, d |) = apply_checker_result_k r in

    let br_name = if is_then then "then" else "else" in

    if hyp `Set.mem` freevars_st br
    then fail g (Some br.range)
           (Printf.sprintf "check_if: branch hypothesis is in freevars of checked %s branch" br_name)
    else (| br, c, d |)
  in

  let (| e1, c1, e1_typing |) = check_branch tm_true e1 true in
  let (| e2, c2, e2_typing |) = check_branch tm_false e2 false in    
  let (| c, e1_typing, e2_typing |) =
    combine_if_branches _ _ _ e1_typing _ _ _ e2_typing in

  let c_typing = 
    let x = fresh g in
    if x `Set.mem` freevars post //exclude this
    then fail g None "Impossible: check_if: unexpected freevar in post, please file a bug-report"
    else if not (eq_tm (comp_res c) post_hint.ret_ty &&
                 eq_univ (comp_u c) post_hint.u &&
                 eq_tm (comp_post c) post_hint.post) //exclude by check' strengthening
    then fail g None
           (Printf.sprintf "check_if: computation type after combining branches does not match post hint,\
                            computed: (%s, %s, %s), expected (%s, %s, %s)"
              (P.univ_to_string (comp_u c)) (P.term_to_string (comp_res c)) (P.term_to_string (comp_post c))
              (P.univ_to_string post_hint.u) (P.term_to_string post_hint.ret_ty) (P.term_to_string post_hint.post))
    else
        let post_typing = post_hint_typing g post_hint x in
        intro_comp_typing g c pre_typing post_typing.ty_typing x post_typing.post_typing
  in

  let d : st_typing_in_ctxt g pre (Some post_hint) =
    (| _, c, T_If g b e1 e2 c _ hyp (E b_typing) e1_typing e2_typing (E c_typing) |) in

  checker_result_for_st_typing d res_ppname
