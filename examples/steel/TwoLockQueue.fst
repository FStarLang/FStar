module TwoLockQueue
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
open  Steel.SpinLock
module L = FStar.List.Tot
module U = Steel.Utils
module Q = Queue

[@@__reduce__]
let full = full_perm
[@@__reduce__]
let half = half_perm full
let fst x = fst x
let snd x = snd x

#push-options "--__temp_no_proj TwoLockQueue"
noeq
type q_ptr (a:Type) = {
  ptr : ref (Q.t a);
  ghost: ghost_ref (Q.t a);
  lock: lock (h_exists (fun (v:FStar.Ghost.erased (Q.t a)) ->
                    pts_to ptr full v `star`
                    ghost_pts_to ghost half v));
}
#pop-options
open FStar.Ghost
[@@__reduce__]
let queue_invariant (#a:_) (head tail:q_ptr a) =
  h_exists (fun (ht: erased (Q.t a & Q.t a)) ->
    ghost_pts_to head.ghost half (hide (fst (reveal ht))) `star`
    ghost_pts_to tail.ghost half (hide (snd (reveal ht))) `star`
    Q.queue (hide (fst (reveal ht))) (hide (snd (reveal ht))))

let pack_queue_invariant (#a:_) (#u:_) (x:erased (Q.t a)) (y:erased (Q.t a)) (head tail:q_ptr a)
 : SteelAtomicT unit u unobservable
   (ghost_pts_to head.ghost half x `star`
    ghost_pts_to tail.ghost half y `star`
    Q.queue x y)
   (fun _ -> queue_invariant head tail)
 = let w = Ghost.hide (Ghost.reveal x, Ghost.reveal y) in
   change_slprop
    (ghost_pts_to head.ghost half x `star`
     ghost_pts_to tail.ghost half y `star`
     Q.queue x y)
    (ghost_pts_to head.ghost half (hide (fst (reveal w))) `star`
     ghost_pts_to tail.ghost half (hide (snd (reveal w))) `star`
     Q.queue (hide (fst (reveal w))) (hide (snd (reveal w))))
    (fun _ -> ());
   intro_exists w (fun w -> ghost_pts_to head.ghost half (hide (fst (reveal w))) `star`
                         ghost_pts_to tail.ghost half (hide (snd (reveal w))) `star`
                         Q.queue (hide (fst (reveal w))) (hide (snd (reveal w))))


noeq
type t (a:Type0) = {
  head : q_ptr a;
  tail : q_ptr a;
  inv : inv (queue_invariant head tail)
}

let new_qptr (#a:_) (q:Q.t a)
  : SteelT (q_ptr a)
           emp
           (fun qp -> ghost_pts_to qp.ghost half q)
  = let ptr = alloc q in
    let ghost = ghost_alloc q in
    ghost_share ghost;
    intro_exists (Ghost.hide q)
                 (fun q -> pts_to ptr full q `star` ghost_pts_to ghost half q);
    let lock = Steel.SpinLock.new_lock (h_exists (fun q -> pts_to ptr full q `star` ghost_pts_to ghost half q)) in
    let res = { ptr; ghost; lock} in
    change_slprop (ghost_pts_to ghost half q)
                  (ghost_pts_to res.ghost half q)
                  (fun _ -> ());
    res

let new_queue (#a:_) (x:a)
  : SteelT (t a) emp (fun _ -> emp)
  = let hd = Q.new_queue x in
    let head = new_qptr hd in
    let tail = new_qptr hd in
    pack_queue_invariant _ _ head tail;
    let inv = new_invariant Set.empty (queue_invariant head tail) in
    { head; tail; inv }

#push-options "--ide_id_info_off"
let enqueue_core (#a:_) (#u:_) (#x:Q.cell a{x.Q.next==null}) (hdl:t a) (tl:Q.t a) (node:Q.t a) (_:unit)
  : SteelAtomicT unit u observable
    (queue_invariant hdl.head hdl.tail `star`
     (ghost_pts_to hdl.tail.ghost half tl `star`
      pts_to node full x))
    (fun _ -> queue_invariant hdl.head hdl.tail `star`
           ghost_pts_to hdl.tail.ghost half node)
  = let open FStar.Ghost in
    let ht' : erased (erased (Q.t a & Q.t a)) = witness_h_exists () in
    let ht : erased (Q.t a & Q.t a) = reveal ht' in
    ghost_gather #_ #_ #half #half #tl #_ hdl.tail.ghost;
    change_slprop (ghost_pts_to hdl.tail.ghost _ _)
                  (ghost_pts_to hdl.tail.ghost full_perm (hide tl))
                  (fun _ -> ());
    change_slprop
        (Q.queue (hide (fst (reveal (reveal ht'))))
                 (hide (snd (reveal (reveal ht')))))
        (Q.queue (hide (fst (reveal ht)))
                 (hide tl))
        (fun _ -> ());
    Q.enqueue tl node;
    ghost_write hdl.tail.ghost node;
    ghost_share hdl.tail.ghost;
    let w = hide (fst (reveal ht), node) in
    change_slprop (Q.queue (hide (fst (reveal ht))) (hide node) `star`
                   ghost_pts_to hdl.head.ghost (half_perm full_perm) (hide (fst (reveal (reveal ht')))) `star`
                   ghost_pts_to hdl.tail.ghost (half_perm full_perm) (Ghost.hide node))
                  (Q.queue (hide (fst (reveal w))) (hide (snd (reveal w))) `star`
                   ghost_pts_to hdl.head.ghost half (hide (fst (reveal w))) `star`
                   ghost_pts_to hdl.tail.ghost half (hide (snd (reveal w))))
                  (fun _ -> ());
    Steel.Effect.Atomic.intro_exists w (fun w -> (ghost_pts_to hdl.head.ghost half (hide (fst (reveal w))) `star`
                                               ghost_pts_to hdl.tail.ghost half (hide (snd (reveal w))) `star`
                                               Q.queue (hide (fst (reveal w))) (hide (snd (reveal w)))))


let enqueue (#a:_) (hdl:t a) (x:a)
  : SteelT unit emp (fun _ -> emp)
  = Steel.SpinLock.acquire hdl.tail.lock;
    let vv : erased (erased (Q.t a)) = witness_h_exists () in
    let v = reveal vv in
    change_slprop
      (pts_to hdl.tail.ptr full (Ghost.reveal vv))
      (pts_to hdl.tail.ptr full v)
      (fun _ -> ());
    change_slprop
      (ghost_pts_to hdl.tail.ghost half (Ghost.reveal vv))
      (ghost_pts_to hdl.tail.ghost half v)
      (fun _ -> ());
    let tl = read hdl.tail.ptr in
    change_slprop
      (ghost_pts_to hdl.tail.ghost half v)
      (ghost_pts_to hdl.tail.ghost half tl)
      (fun _ -> ());
    let cell = Q.({ data = x; next = null} ) in
    let node = alloc cell in
    slassert (ghost_pts_to hdl.tail.ghost half tl `star`
              pts_to node full_perm cell);
    with_invariant #_ #_ #_ #Set.empty #_ #_ hdl.inv (enqueue_core hdl tl node);
    write hdl.tail.ptr node;
    slassert (pts_to hdl.tail.ptr full_perm (Ghost.hide node) `star`
              ghost_pts_to hdl.tail.ghost half (Ghost.hide node));
    Steel.Effect.Atomic.intro_exists (Ghost.hide node) (fun n -> pts_to hdl.tail.ptr full_perm n `star`
                                                              ghost_pts_to hdl.tail.ghost half n);
    Steel.SpinLock.release hdl.tail.lock
