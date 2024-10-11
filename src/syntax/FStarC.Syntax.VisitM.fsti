module FStarC.Syntax.VisitM

open FStarC.Syntax.Syntax
open FStarC.Class.Monad

// TODO: add a way to specify what happens when we traverse a binder,
// hopefully allowing the user to choose whether we open/close or not,
// and know the binding depth at each point.

val visitM_term
  (#m:_) {| monad m |}
  (proc_quotes : bool)
  (v : term -> m term)
  (t : term)
  : m term

val visitM_term_univs
  (#m:_) {| monad m |}
  (proc_quotes : bool)
  (vt : term -> m term)
  (vu : universe -> m universe)
  (t : term)
  : m term

val visitM_sigelt
  (#m:_) {| monad m |}
  (proc_quotes : bool)
  (vt : term -> m term)
  (vu : universe -> m universe)
  (t : sigelt)
  : m sigelt
