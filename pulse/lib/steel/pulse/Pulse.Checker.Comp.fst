module Pulse.Checker.Comp

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base

module FV = Pulse.Typing.FV

let check_comp (g:env) 
               (c:comp_st)
               (pre_typing:tot_typing g (comp_pre c) tm_vprop)
  : T.Tac (comp_typing g c (comp_u c))
  = let check_st_comp (st:st_comp { comp_u c == st.u /\
                                    comp_pre c == st.pre /\
                                    comp_res c == st.res /\
                                    comp_post c == st.post } )
      : T.Tac (st_comp_typing g st)
      = let (| u, t_u |) = check_universe g st.res in 
        if not (eq_univ u (comp_u c))
        then fail g None "Unexpected universe"
        else (
          let x = fresh g in
          let px = v_as_nv x in
          assume (~(x `Set.mem` freevars (comp_post c)));
          let gx = push_binding g x (fst px) st.res in
          let (| ty, post_typing |) = core_check_term gx (open_term_nv (comp_post c) px) in
          if not (eq_tm ty tm_vprop)
          then fail g None "Ill-typed postcondition"
          else (
            assert (ty == tm_vprop);
            STC g st x t_u pre_typing (E post_typing)
          )
        )
    in
    match c with
    | C_ST st -> 
      let stc = check_st_comp st in
      CT_ST _ _ stc
    | C_STAtomic i st -> 
      let stc = check_st_comp st in
      let (| ty, i_typing |) = core_check_term g i in
      if not (eq_tm ty tm_inames)
      then fail g None "Ill-typed inames"
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = check_st_comp st in
      let (| ty, i_typing |) = core_check_term g i in
      if not (eq_tm ty tm_inames)
      then fail g None "Ill-typed inames"
      else CT_STGhost _ _ _ (E i_typing) stc