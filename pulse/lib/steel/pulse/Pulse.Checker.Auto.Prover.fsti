module Pulse.Checker.Auto.Prover
open Pulse.Syntax
open Pulse.Typing
module T = FStar.Tactics

noeq
type framing_failure = {
  unmatched_preconditions : list term;
  remaining_context : list term;
}

(* t is well-typed in g at c, where the context has ctxt:vprop.

   Tries to transform the context ctxt to ctxt',
   by applying various proof steps, including:
     * Introducing existential and pure vprops
     * Unfolding and folding definitions
     * Calling into F* to prove that certain terms are provably equal.
   Such that
      ctxt' has the form c.pre * frame

   Returns an elaboration of t, preceding it with the necessary proof steps
   and a proof that the elaboration is well-typed in the oringal context
   
   Or, a framing failure, showing which conjuncts of the c.pre could not be
   derived
*)
val prove_precondition (#g:env)
                       (#ctxt:term)
                       (ctxt_typing: tot_typing g ctxt Tm_VProp)
                       (#t:st_term)
                       (#c:comp_st)
                       (t_typing: st_typing g t c)
  : T.Tac 
    (either 
        (t:st_term &
         c:comp_st { comp_pre c == ctxt } &
         st_typing g t c)
        framing_failure)
