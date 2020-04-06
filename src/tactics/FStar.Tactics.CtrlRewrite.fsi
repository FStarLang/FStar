#light "off"
module FStar.Tactics.CtrlRewrite

open FStar.Syntax.Syntax
open FStar.Tactics.Types
open FStar.Tactics.Monad

module Z = FStar.BigInt

(* TODO: allow to pass information from ctrl_tac to rewriter? *)
type controller_ty = term -> tac<(bool * ctrl_flag)>
type rewriter_ty   = tac<unit>

val ctrl_rewrite: direction -> controller_ty -> rewriter_ty -> tac<unit>
