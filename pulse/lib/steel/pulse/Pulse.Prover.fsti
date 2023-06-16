module Pulse.Prover

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Util
open Pulse.Prover.Common

val prover : prover_t

val prove_precondition (#g:env) (#ctxt:term)
  (ctxt_typing:vprop_typing g ctxt)
  (#t:st_term) (#c:comp_st)
  (t_typing:st_typing g t c)
  : T.Tac (option (t:st_term &
                   c:comp_st { comp_pre c == ctxt } &
                   st_typing g t c))
