module Pulse.Checker.Comp

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer

let check (g:env) 
          (c:comp_st)
          (pre_typing:tot_typing g (comp_pre c) tm_vprop)
  : T.Tac (comp_typing g c (comp_u c))
  = let g = Pulse.Typing.Env.push_context_no_range g "check_comp"  in
  
    let check_st_comp (st:st_comp { comp_u c == st.u /\
                                    comp_pre c == st.pre /\
                                    comp_res c == st.res /\
                                    comp_post c == st.post } )
      : T.Tac (st_comp_typing g st)
      = let (| u, t_u |) = check_universe g st.res in 
        if not (eq_univ u (comp_u c))
        then fail g None
              (Printf.sprintf "check_comp: computed universe of %s as %s, whereas annotated as %s"
                 (P.term_to_string st.res)
                 (P.univ_to_string u)
                 (P.univ_to_string (comp_u c)))

        else (
          let x = fresh g in
          let px = v_as_nv x in
          assume (~(x `Set.mem` freevars (comp_post c)));
          let gx = push_binding g x (fst px) st.res in
          let (| ty, post_typing |) = core_check_term gx (open_term_nv (comp_post c) px) in
          if not (eq_tm ty tm_vprop)
          then fail g None
                 (Printf.sprintf "check_comp: ill-typed postcondition %s" (P.term_to_string (comp_post c)))
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
      then fail g None
             (Printf.sprintf "check_comp: type of inames term %s is %s, expected %s"
                (P.term_to_string i) (P.term_to_string ty) (P.term_to_string tm_inames))
      else CT_STAtomic _ _ _ (E i_typing) stc
    | C_STGhost i st -> 
      let stc = check_st_comp st in
      let (| ty, i_typing |) = core_check_term g i in
      if not (eq_tm ty tm_inames)
      then fail g None
             (Printf.sprintf "check_comp: type of inames term %s is %s, expected %s"
                (P.term_to_string i) (P.term_to_string ty) (P.term_to_string tm_inames))
      else CT_STGhost _ _ _ (E i_typing) stc
