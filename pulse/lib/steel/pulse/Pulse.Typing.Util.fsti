module Pulse.Typing.Util

open FStar.Tactics.V2

(* Like T.check_equiv, but will make sure to not delay any VC. *)
val check_equiv_now : g:env -> t1:term -> t2:term ->
  Tac (option (equiv_token g t1 t2) & issues)

(* Like T.universe_of, but will make sure to not delay any VC. *)
val universe_of_now : g:env -> e:term ->
  Tac (option (u:universe{typing_token g e (E_Total, pack_ln (Reflection.V2.Tv_Type u))}) & issues)
