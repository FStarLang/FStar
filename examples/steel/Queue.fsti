module Queue
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module L = FStar.List.Tot
module U = Steel.Utils

#push-options "--__no_positivity"
noeq
type cell (a:Type0) = {
  data : a;
  next : t a;
}
and t a = ref (cell a)
#pop-options

let pts_to (#a:_) (x:t a) (v: cell a) = pts_to x full_perm v

val queue_l (#a:_) (hd tl:Ghost.erased (t a)) (l:Ghost.erased (list a))
  : slprop u#1

let queue (#a:_) (hd:Ghost.erased (t a)) (tl:Ghost.erased (t a)) = h_exists (queue_l hd tl)

val new_queue (#a:_) (v:a) :
  SteelT (t a) emp (fun x -> queue x x)

val enqueue (#a:_) (#u:_) (#hd:Ghost.erased (t a)) (tl:t a) (#v:_) (last:t a)
  : SteelAtomic unit u observable
                (queue hd tl `star` pts_to last v)
                (fun _ -> queue hd last)
                (requires fun _ -> v.next == null)
                (ensures fun _ _ _ -> True)

val dequeue (#a:_) (#u:_) (#tl:Ghost.erased (t a)) (hd:t a)
  : SteelAtomicT (option (t a)) u observable
                 (queue hd tl)
                 (fun res ->
                   match res with
                   | None ->
                     queue hd tl
                   | Some p ->
                     h_exists (fun c -> pts_to p c `star` queue c.next tl))
