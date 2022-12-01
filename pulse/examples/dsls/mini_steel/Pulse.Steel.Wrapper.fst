module Pulse.Steel.Wrapper

open Steel.ST.Effect
open Steel.Memory
open Steel.ST.Util

type stt (a:Type u#a) (pre:vprop) (post:a -> vprop) = unit -> STT a pre post

let return_stt (#a:Type u#a) (x:a) : stt a emp (fun r -> pure (r == x)) =
  fun _ -> return x

let return_stt_noeq (#a:Type u#a) (x:a) : stt a emp (fun _ -> emp) = fun _ -> return x

let bind_stt (#a:Type u#a) (#b:Type u#b) (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt a pre1 post1)
  (e2:(x:a -> stt b (post1 x) post2))

  : stt b pre1 post2 =

  fun _ ->
  let x = e1 () in
  e2 x ()

let frame_stt (#a:Type u#a) (#pre:vprop) (#post:a -> vprop) (frame:vprop) (e:stt a pre post)
  : stt a (pre `star` frame) (fun x -> post x `star` frame) =

  fun _ -> e ()

assume val admit__ (#a:Type u#a) (#p:vprop) (#q:a -> vprop) (_:unit) : ST a p q True (fun _ -> False)

let sub_stt (#a:Type u#a) (#pre1:vprop) (pre2:vprop) (#post1:a -> vprop) (post2:a -> vprop)
  (e:stt a pre1 post1)
  : stt a pre2 post2 =
  fun _ ->
  admit__ ()
