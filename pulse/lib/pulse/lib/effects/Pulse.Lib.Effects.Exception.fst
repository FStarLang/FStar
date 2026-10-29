module Pulse.Lib.Effects.Exception

open Pulse.Lib.Core
module E = Pulse.Lib.Effects.Core

let throw #other #exn #ops #exceptional #g #a #q e =
  E.Abort #(tag other) #(extend ops exceptional) Throw e

inline_for_extraction
let rec handle_same (#other #exn:Type0) (#ops:E.signature other)
  (#exceptional:exn -> slprop) (#g:E.grade) (#a #b:Type0)
  (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:prog ops exceptional g a p q)
  ([@@@FStar.Attributes.monomorphize] normal:(x:a -> E.tree ops g b (q x) s))
  ([@@@FStar.Attributes.monomorphize] caught:(e:exn -> E.tree ops g b (exceptional e) s))
  : Tot (E.tree ops g b p s) (decreases c) =
  match c with
  | E.Return x -> normal x
  | E.Step action k -> E.Step action (fun x -> handle_same (k x) normal caught)
  | E.Perform #_ #_ #_ #_ #_ #f op arg k ->
      (match op with
      | Other op ->
          E.Perform #other #ops #g #b #s #f op arg
            (fun y -> handle_same (k y) normal caught))
  | E.Abort op arg ->
      (match op with
      | Throw -> caught arg
      | Other op -> E.Abort #other #ops op arg)

let handle #other #exn #ops #exceptional #g #h #a #b #p #q #s c normal caught =
  handle_same (E.weaken_grade (E.join g h) c)
    (fun x -> E.weaken_grade (E.join g h) (normal x))
    (fun e -> E.weaken_grade (E.join g h) (caught e))

let framed_layer #other #exn #ops #exceptional #g #a #p #q f c =
  E.relabel #(tag other) #(tag other)
    #(E.frame_signature f (extend ops exceptional))
    #(extend (E.frame_signature f ops) (fun e -> exceptional e ** f))
    (fun op -> match op with
      | Throw ->
          assert_norm (
            extend (E.frame_signature f ops) (fun e -> exceptional e ** f) Throw ==
            E.frame_signature f (extend ops exceptional) Throw);
          Throw
      | Other op -> Other op)
    c

let frame #other #exn #ops #exceptional #g #a #p #q f c =
  framed_layer f (E.frame f c)

let weaken #other #exn #ops #exceptional #g #a #p #q c =
  E.relabel #other #(tag other) #ops #(extend ops exceptional) (fun op -> Other op) c
