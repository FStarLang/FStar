module Pulse.Lib.Effects.Exception

open Pulse.Lib.Core
module E = Pulse.Lib.Effects.Core

type tag (other:Type0) = | Throw | Other : op:other -> tag other

let extend (#other #exn:Type0) (ops:E.signature other)
  (exceptional:exn -> slprop) : E.signature (tag other) =
  fun op -> match op with
  | Throw -> E.Aborting exn exceptional
  | Other op -> ops op

let prog (#other #exn:Type0) (ops:E.signature other)
  (exceptional:exn -> slprop) (g:E.grade) (a:Type0)
  (p:slprop) (q:a -> slprop) =
  E.tree (extend ops exceptional) g a p q

inline_for_extraction
val throw (#other #exn:Type0) (#ops:E.signature other)
  (#exceptional:exn -> slprop) (#g:E.grade) (#a:Type0) (#q:a -> slprop)
  (e:exn) : prog ops exceptional g a (exceptional e) q

// Clauses run outside this layer and can raise in an enclosing layer.
// Abort has no private frame, so no whole-tree policy or frame-polymorphic
// clause is necessary. Every other operation is forwarded with its kind intact.
inline_for_extraction
val handle (#other #exn:Type0) (#ops:E.signature other)
  (#exceptional:exn -> slprop) (#g #h:E.grade) (#a #b:Type0)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:prog ops exceptional g a p q)
  ([@@@FStar.Attributes.monomorphize] normal:(x:a -> E.tree ops h b (q x) s))
  ([@@@FStar.Attributes.monomorphize] caught:(e:exn -> E.tree ops h b (exceptional e) s))
  : E.tree ops (E.join g h) b p s

// In particular, framing a nested computation strengthens outer exceptions,
// not just the exception introduced by this layer.
inline_for_extraction
val framed_layer (#other #exn:Type0) (#ops:E.signature other)
  (#exceptional:exn -> slprop) (#g:E.grade) (#a:Type0)
  (#p:slprop) (#q:a -> slprop) (f:slprop)
  (c:E.tree (E.frame_signature f (extend ops exceptional)) g a p q)
  : prog (E.frame_signature f ops) (fun e -> exceptional e ** f) g a p q

inline_for_extraction
val frame (#other #exn:Type0) (#ops:E.signature other)
  (#exceptional:exn -> slprop) (#g:E.grade) (#a:Type0)
  (#p:slprop) (#q:a -> slprop) (f:slprop)
  (c:prog ops exceptional g a p q)
  : prog (E.frame_signature f ops) (fun e -> exceptional e ** f)
      g a (p ** f) (fun x -> q x ** f)

inline_for_extraction
val weaken (#other #exn:Type0) (#ops:E.signature other)
  (#exceptional:exn -> slprop) (#g:E.grade) (#a:Type0)
  (#p:slprop) (#q:a -> slprop) (c:E.tree ops g a p q)
  : prog ops exceptional g a p q
