module Queue
include Queue.Def
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot
module U = Steel.Utils

let pts_to (#a:_) (x:t a) ([@@@smt_fallback]v: Ghost.erased (cell a)) = pts_to x full_perm v

val queue_l (#a:_) (hd tl:Ghost.erased (t a)) (l:Ghost.erased (list a))
  : slprop u#1

let queue (#a:_) ([@@@smt_fallback] hd:Ghost.erased (t a))
                 ([@@@smt_fallback] tl:Ghost.erased (t a)) = h_exists (queue_l hd tl)

val new_queue (#a:_) (v:a) :
  SteelT (t a) emp (fun x -> queue x x)

(*
   tl -> { data; next=Null }

---

assume atomic field update primitive:
   set_next #v (x:t a) (nxt:t a)
     : SteelAtomic unit _ _ (pts_to x v)
                            (pts_to x {v with next = nxt})






 let c = read tl in
 wriet (c.next) = last
*)
val enqueue (#a:_) (#u:_) (#hd:Ghost.erased (t a)) (tl:t a) (#v:Ghost.erased (cell a)) (last:t a)
  : SteelAtomic unit u observable
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

val dequeue (#a:_) (#u:_) (#tl:Ghost.erased (t a)) (hd:t a)
  : SteelAtomicT (option (t a)) u observable
                 (queue hd tl)
                 (dequeue_post tl hd)
