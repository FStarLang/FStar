module Queue
include Queue.Def
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot
module U = Steel.Utils

/// This module provides a library for queues of elements, with the standard enqueue and dequeue operations, which we use in TwoLockQueue to model Michael and Scott's concurrent two lock queue.
/// We only prove that this implementation is safe, and do not specify functional correctness here

/// This library does not allow sharing ownership of the queue. As such, fractional permissions
/// in this module will not be useful, and we use this wrapper to avoid specifying them
let pts_to (#a:_) (x:t a) ([@@@smt_fallback]v: Ghost.erased (cell a)) = pts_to x full_perm v

/// The core queue separation logic predicate.
/// It is indexed by a head and tail pointer.
val queue (#a:_) ([@@@smt_fallback] hd:Ghost.erased (t a))
                 ([@@@smt_fallback] tl:Ghost.erased (t a)) : vprop

/// Creating a new queue containing element [v].
val new_queue (#a:_) (v:a) :
  SteelT (t a) emp (fun x -> queue x x)

(*
   tl -> { data; next=Null }

---Queue

assume atomic field update primitive:
   set_next #v (x:t a) (nxt:t a)
     : SteelAtomic unit _ _ (pts_to x v)
                            (pts_to x {v with next = nxt})






 let c = read tl in
 wriet (c.next) = last
*)

/// The correctness of Michael and Scott's two lock queue relies on an atomic field update operation.
/// Steel's memory model does not consider that such updates are atomic.
/// Thus, inside the implementation, we assume that such an atomic operation exists.
/// This is then used to provide this atomic enqueue function, adding cell [last] to the queue.
val enqueue (#a:_) (#u:_) (#hd:Ghost.erased (t a)) (tl:t a) (#v:Ghost.erased (cell a)) (last:t a)
  : SteelAtomic unit u
                (queue hd tl `star` pts_to last v)
                (fun _ -> queue hd last)
                (requires fun _ -> v.next == null)
                (ensures fun _ _ _ -> True)

(*
  queue hd tl ==equiv==

  hd -> {data=_; next=_} * (if next == null then pure (hd == tl) else queue next tl)

assume atomic field update primitive:
   read_next #v (x:t a) (nxt:t a)
     : SteelAtomic unit _ _ (pts_to x v)
                            (pts_to x {v with next = nxt})

*)
[@@__reduce__]
let dequeue_post_success (#a:_) ([@@@smt_fallback]tl:Ghost.erased (t a))
                                ([@@@smt_fallback]hd:t a)
                                ([@@@smt_fallback]p:t a) =
      h_exists (fun (c:Ghost.erased (cell a)) -> pts_to hd c `star` pure (Ghost.reveal p == c.next) `star` queue p tl)

let dequeue_post (#a:_) ([@@@smt_fallback]tl:Ghost.erased (t a))
                        ([@@@smt_fallback]hd:t a)
                        ([@@@smt_fallback]res:option (t a)) =
    match res with
    | None ->
      queue hd tl
    | Some p ->
      dequeue_post_success tl hd p

/// Similarly to the `enqueue` function above, we implement an atomic `dequeue` function,
/// which fails while leaving the queue unchanged if the queue is empty
val dequeue (#a:_) (#u:_) (#tl:Ghost.erased (t a)) (hd:t a)
  : SteelAtomicT (option (t a)) u
                 (queue hd tl)
                 (dequeue_post tl hd)
