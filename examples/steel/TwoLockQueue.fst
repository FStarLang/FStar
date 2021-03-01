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

let rewrite #u (p q:slprop)
  : SteelAtomic unit u unobservable p (fun _ -> q)
    (requires fun _ -> p `equiv` q)
    (ensures fun _ _ _ -> True)
  = change_slprop p q (fun _ -> ())

open FStar.Ghost
let witness_h_exists' (#a:Type) (#opened_invariants:_) (#p:Ghost.erased a -> slprop) (_:unit)
  : SteelAtomicT (Ghost.erased a) opened_invariants unobservable
                 (h_exists p) p
  = let v : erased (erased a)  = witness_h_exists () in
    reveal v

[@@__reduce__]
let lock_inv #a (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t a)) =
    h_exists (fun (v:FStar.Ghost.erased (Q.t a)) ->
                    pts_to ptr full v `star`
                    ghost_pts_to ghost half v)

let intro_lock_inv #a #u (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t a))
  : SteelAtomicT unit u unobservable
    (h_exists (fun (v:FStar.Ghost.erased (Q.t a)) ->
                    pts_to ptr full v `star`
                    ghost_pts_to ghost half v))
    (fun _ -> lock_inv ptr ghost)
  = rewrite_context()

noeq
type q_ptr (a:Type) = {
  ptr : ref (Q.t a);
  ghost: ghost_ref (Q.t a);
  lock: lock (lock_inv ptr ghost);
}

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
   rewrite
    (Q.queue x y)
    (Q.queue (hide (fst (reveal w))) (hide (snd (reveal w))));
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
    intro_exists _ (fun q -> pts_to ptr full q `star` ghost_pts_to ghost half q);
    let lock = Steel.SpinLock.new_lock _ in
    { ptr; ghost; lock}


let new_queue (#a:_) (x:a)
  : SteelT (t a) emp (fun _ -> emp)
  = let hd = Q.new_queue x in
    let head = new_qptr hd in
    let tail = new_qptr hd in
    pack_queue_invariant _ _ head tail;
    let inv = new_invariant _ _ in
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
    let ht : erased (Q.t a & Q.t a) = witness_h_exists' () in
    ghost_gather #_ #_ #half #half #tl #_ hdl.tail.ghost;
    rewrite
      (ghost_pts_to hdl.tail.ghost _ _)
      (ghost_pts_to hdl.tail.ghost full_perm (hide tl));
    rewrite
      (Q.queue (hide (fst (reveal ht)))
               (hide (snd (reveal ht))))
      (Q.queue (hide (fst (reveal ht)))
               (hide tl));
    Q.enqueue tl node;
    ghost_write hdl.tail.ghost node;
    ghost_share hdl.tail.ghost;
    let w = hide (fst (reveal ht), node) in
    rewrite
      (Q.queue (hide (fst (reveal ht))) (hide node))
      (Q.queue (hide (fst (reveal w))) (hide (snd (reveal w))));
    Steel.Effect.Atomic.intro_exists w (fun w -> (ghost_pts_to hdl.head.ghost half (hide (fst (reveal w))) `star`
                                               ghost_pts_to hdl.tail.ghost half (hide (snd (reveal w))) `star`
                                               Q.queue (hide (fst (reveal w))) (hide (snd (reveal w)))))

let enqueue (#a:_) (hdl:t a) (x:a)
  : SteelT unit emp (fun _ -> emp)
  = Steel.SpinLock.acquire hdl.tail.lock;
    let v : erased (Q.t a) = witness_h_exists' () in
    let tl = read hdl.tail.ptr in
    rewrite
      (ghost_pts_to hdl.tail.ghost half v)
      (ghost_pts_to hdl.tail.ghost half tl);
    let cell = Q.({ data = x; next = null} ) in
    let node = alloc cell in
    // slassert (ghost_pts_to hdl.tail.ghost half tl `star`
    //           pts_to node full_perm cell);
    with_invariant hdl.inv (enqueue_core hdl tl node);
    write hdl.tail.ptr node;
    // slassert (pts_to hdl.tail.ptr full_perm (Ghost.hide node) `star`
    //           ghost_pts_to hdl.tail.ghost half (Ghost.hide node));
    Steel.Effect.Atomic.intro_exists (Ghost.hide node) (fun n -> pts_to hdl.tail.ptr full_perm n `star`
                                                              ghost_pts_to hdl.tail.ghost half n);
    Steel.SpinLock.release hdl.tail.lock

let maybe_ghost_pts_to #a (x:ghost_ref (Q.t a)) (hd:Q.t a) (o:option (Q.t a)) =
  match o with
  | None -> ghost_pts_to x half hd
  | Some next -> ghost_pts_to x half next `star` (h_exists (pts_to hd full_perm))

let elim_pure (#p:prop) #u ()
  : SteelAtomic unit u unobservable
                (pure p) (fun _ -> emp)
                (requires fun _ -> True)
                (ensures fun _ _ _ -> p)
  = let _ = Steel.Effect.Atomic.elim_pure p in ()

module T = FStar.Tactics
#push-options "--query_stats --log_queries"
let dequeue_core (#a:_) (#u:_) (hdl:t a) (hd:Q.t a) (_:unit)
  : SteelAtomicT (option (Q.t a)) u observable
    (queue_invariant hdl.head hdl.tail `star`
     ghost_pts_to hdl.head.ghost half hd)
    (fun o ->
      queue_invariant hdl.head hdl.tail `star`
      maybe_ghost_pts_to hdl.head.ghost hd o)
  = let ht = witness_h_exists' () in
    ghost_gather #_ #_ #half #half #hd #_ hdl.head.ghost;
    rewrite
      (ghost_pts_to hdl.head.ghost _ _)
      (ghost_pts_to hdl.head.ghost full_perm (hide hd));
    let tl = (hide (snd (reveal ht))) in
    rewrite
        (Q.queue (hide (fst (reveal ht)))
                 (hide (snd (reveal ht))))
        (Q.queue (hide hd) tl);
    rewrite
        (ghost_pts_to hdl.tail.ghost (half_perm full_perm) _)
        (ghost_pts_to hdl.tail.ghost (half_perm full_perm) tl);
    let o = Queue.dequeue #_ #_ #tl hd in
    match o with
    | None ->
      rewrite
        (Q.dequeue_post _ _ _)
        (Q.queue (hide hd) tl);
      ghost_share hdl.head.ghost;
      pack_queue_invariant _ _ hdl.head hdl.tail;
      rewrite
        (ghost_pts_to hdl.head.ghost _ _)
        (maybe_ghost_pts_to hdl.head.ghost hd o);
      o

    | Some p ->
      rewrite
        (Q.dequeue_post _ _ _)
        (Q.dequeue_post_success tl hd p);
      let c = witness_h_exists' () in
      // slassert (pts_to hd full_perm c `star` pure (Ghost.reveal p == c.Q.next) `star` Q.queue p tl);
      elim_pure ();
      intro_exists c (pts_to hd full_perm);
      ghost_write hdl.head.ghost p;
      ghost_share hdl.head.ghost;
      pack_queue_invariant _ _ hdl.head hdl.tail;
      // slassert (ghost_pts_to hdl.head.ghost _ _ `star` h_exists (pts_to hd full_perm));
      rewrite
        (ghost_pts_to hdl.head.ghost _ _ `star` h_exists (pts_to hd full_perm))
        (maybe_ghost_pts_to hdl.head.ghost hd o);
      o

let dequeue (#a:_) (hdl:t a)
  : SteelT (option a) emp (fun _ -> emp)
  = Steel.SpinLock.acquire hdl.head.lock;
    let v : erased (Q.t a) = witness_h_exists' () in
    let hd = read hdl.head.ptr in
    let o = with_invariant hdl.inv (dequeue_core hdl hd) in
    match o with
    | None ->
      rewrite
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half hd);
      intro_exists _ (fun (v:erased (Q.t a)) -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      Steel.SpinLock.release hdl.head.lock;
      None

    | Some next ->
      rewrite
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half next `star` h_exists (pts_to hd full_perm));
      let c = witness_h_exists' () in
      write hdl.head.ptr next;
      intro_exists _ (fun (v:erased (Q.t a)) -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      Steel.SpinLock.release hdl.head.lock;
      let c = read hd in
      let v = c.Q.data in
      free hd;
      Some v
