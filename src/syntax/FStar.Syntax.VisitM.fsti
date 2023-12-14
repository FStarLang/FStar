module FStar.Syntax.VisitM

open FStar.Syntax.Syntax
open FStar.Class.Monad

// TODO: add a way to specify what happens when we traverse a binder,
// hopefully allowing the user to choose whether we open/close or not,
// and know the binding depth at each point.

val visitM_term
  (#m:_) {| monad m |}
  (v : term -> m term)
  (t : term)
  : m term

val visitM_sigelt
  (#m:_) {| monad m |}
  (v : term -> m term)
  (t : sigelt)
  : m sigelt