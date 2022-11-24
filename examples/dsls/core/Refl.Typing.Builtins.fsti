module Refl.Typing.Builtins

module R = FStar.Reflection
module T = FStar.Tactics

val subtyping_token (g:R.env) (t0 t1:R.typ) : Type0

val equiv_token (g:R.env) (t0 t1:R.typ) : Type0

val typing_token (g:R.env) (e:R.term) (t:R.typ) : Type0

val check_subtyping (g:R.env) (t0 t1:R.typ)
  : T.Tac (option (squash (subtyping_token g t0 t1)))

val check_equiv (g:R.env) (t0 t1:R.typ)
  : T.Tac (option (squash (equiv_token g t0 t1)))

val tc_term (g:R.env) (e:R.term)
  : T.Tac (option (t:R.typ{typing_token g e t}))
