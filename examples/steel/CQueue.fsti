module CQueue
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot

val t (a: Type0) : Tot Type0

noextract
val v (a: Type0) : Tot Type0

noextract
val datas (#a: Type0) (l: v a) : Tot (list a)

val queue (#a: Type) (x: t a) (l: Ghost.erased (v a)) : Tot (slprop u#1)

val create_queue (a: Type) : Steel (t a & Ghost.erased (v a)) emp (fun x -> queue (fst x) (snd x))
  (requires (fun _ -> True))
  (ensures (fun _ res _ -> datas (snd res) == []))

val enqueue
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (v a))
  (w: a)
: Steel (Ghost.erased (v a))
    (queue x l)
    (fun res -> queue x res)
    (requires (fun _ -> True))
    (ensures (fun _ res _ -> datas res == datas l `L.append` [w]))

val queue_is_empty
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (v a))
: Steel bool
    (queue x l)
    (fun _ -> queue x l)
    (requires (fun _ -> True))
    (ensures (fun _ res _ ->
      res == Nil? (datas l)
    ))

val dequeue
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (v a))
: Steel (a & Ghost.erased (v a))
    (queue x l)
    (fun res -> queue x (snd res))
    (requires (fun _ -> Cons? (datas l) == true))
    (ensures (fun _ res _ -> datas l == fst res :: datas (snd res)))
