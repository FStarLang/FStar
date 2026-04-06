module FStarC.Syntax.VisitM

open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Class.Monad

// TODO: add a way to specify what happens when we traverse a binder,
// hopefully allowing the user to choose whether we open/close or not,
// and know the binding depth at each point.

val visitM_term_univs
  (#m:_) {| monad m |}
  (proc_quotes : bool)
  (vt : term -> ML (m term))
  (vu : universe -> ML (m universe))
  (t : term)
  : ML (m term)

val visitM_term
  (#m:_) {| monad m |}
  (proc_quotes : bool)
  (v : term -> ML (m term))
  (t : term)
  : ML (m term)

val visitM_sigelt
  (#m:_) {| monad m |}
  (proc_quotes : bool)
  (vt : term -> ML (m term))
  (vu : universe -> ML (m universe))
  (t : sigelt)
  : ML (m sigelt)
