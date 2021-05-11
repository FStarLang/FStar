module CQueue
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.FractionalPermission
open Steel.SelReference
module L = FStar.List.Tot

(* This file is a Steel model for queues implemented using singly
   linked lists, with a pointer to the tail end of the list, not to
   the actual last element, but to the *pointer* to the last
   element. It models the C implementation in CQueue.c. *)

(* The lvalue type (or type for non-null pointers) for queues. *)

val t (a: Type0) : Tot Type0

(* The high-level value of a queue, should not be used in C code outside of specs.
   Note that this interface provides no way to construct values for this type.
   In fact, the user will only get ghost values from Steel operations below.
*)

noextract
val v (a: Type0) : Tot Type0

noextract
val datas (#a: Type0) (l: v a) : Tot (list a)

val queue (#a: Type) (x: t a) (l: Ghost.erased (v a)) : Tot vprop

val create_queue (a: Type) : SteelSel (t a & Ghost.erased (v a)) emp (fun x -> queue (fst x) (snd x))
  (requires (fun _ -> True))
  (ensures (fun _ res _ -> datas (snd res) == []))

val enqueue
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (v a))
  (w: a)
: SteelSel (Ghost.erased (v a))
    (queue x l)
    (fun res -> queue x res)
    (requires (fun _ -> True))
    (ensures (fun _ res _ -> datas res == datas l `L.append` [w]))

val queue_is_empty
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (v a))
: SteelSel bool
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
: SteelSel (a & Ghost.erased (v a))
    (queue x l)
    (fun res -> queue x (snd res))
    (requires (fun _ -> Cons? (datas l) == true))
    (ensures (fun _ res _ -> datas l == fst res :: datas (snd res)))
