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
open FStar.Ghost
let ghost_gather (#a:Type) (#u:_)
                 (#p0 #p1:perm) (#p:perm{p == sum_perm p0 p1})
                 (x0 #x1:erased a)
                 (r:ghost_ref a)
  : SteelAtomic unit u unobservable
    (ghost_pts_to r p0 x0 `star`
     ghost_pts_to r p1 x1)
    (fun _ -> ghost_pts_to r p x0)
    (requires fun _ -> true)
    (ensures fun _ _ _ -> x0 == x1)
  = let _ = ghost_gather #a #u #p0 #p1 r in ()

let rewrite #u (p q:slprop)
  : SteelAtomic unit u unobservable p (fun _ -> q)
    (requires fun _ -> p `equiv` q)
    (ensures fun _ _ _ -> True)
  = change_slprop p q (fun _ -> ())

let elim_pure (#p:prop) #u ()
  : SteelAtomic unit u unobservable
                (pure p) (fun _ -> emp)
                (requires fun _ -> True)
                (ensures fun _ _ _ -> p)
  = let _ = Steel.Effect.Atomic.elim_pure p in ()

let open_exists (#a:Type) (#opened_invariants:_) (#p:Ghost.erased a -> slprop) (_:unit)
  : SteelAtomicT (Ghost.erased a) opened_invariants unobservable
                 (h_exists p) p
  = let v : erased (erased a)  = witness_h_exists () in
    reveal v

[@@__reduce__]
let lock_inv #a (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t a)) =
    h_exists (fun v ->
      pts_to ptr full v `star`
      ghost_pts_to ghost half v)

let intro_lock_inv #a #u (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t a))
  : SteelAtomicT unit u unobservable
    (h_exists (fun v ->
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

[@@__reduce__]
let queue_invariant (#a:_) ([@@@smt_fallback]head:q_ptr a) ([@@@smt_fallback] tail:q_ptr a) =
  h_exists (fun h ->
  h_exists (fun t ->
    ghost_pts_to head.ghost half h `star`
    ghost_pts_to tail.ghost half t `star`
    Q.queue h t))

let pack_queue_invariant (#a:_) (#u:_) (x:erased (Q.t a)) (y:erased (Q.t a)) (head tail:q_ptr a)
 : SteelAtomicT unit u unobservable
   (ghost_pts_to head.ghost half x `star`
    ghost_pts_to tail.ghost half y `star`
    Q.queue x y)
   (fun _ -> queue_invariant head tail)
 = intro_exists y (fun y -> ghost_pts_to head.ghost half x `star`
                         ghost_pts_to tail.ghost half y `star`
                         Q.queue x y);
   intro_exists x (fun x -> h_exists (fun y -> ghost_pts_to head.ghost half x `star`
                                         ghost_pts_to tail.ghost half y `star`
                                         Q.queue x y))

noeq
type t (a:Type0) = {
  head : q_ptr a;
  tail : q_ptr a;
  inv : inv (queue_invariant head tail)
}


let new_queue (#a:_) (x:a)
  : SteelT (t a) emp (fun _ -> emp)
  = let new_qptr (#a:_) (q:Q.t a)
      : SteelT (q_ptr a) emp (fun qp -> ghost_pts_to qp.ghost half q)
      = let ptr = alloc q in
        let ghost = ghost_alloc q in
        ghost_share ghost;
        intro_exists _ (fun q -> pts_to ptr full q `star` ghost_pts_to ghost half q);
        let lock = Steel.SpinLock.new_lock _ in
        { ptr; ghost; lock}
    in
    let hd = Q.new_queue x in
    let head = new_qptr hd in
    let tail = new_qptr hd in
    pack_queue_invariant _ _ head tail;
    let inv = new_invariant _ _ in
    { head; tail; inv }

#push-options "--ide_id_info_off"
#restart-solver
#push-options "--query_stats --log_queries"
let enqueue (#a:_) (hdl:t a) (x:a)
  : SteelT unit emp (fun _ -> emp)
  = Steel.SpinLock.acquire hdl.tail.lock;
    let v = open_exists () in
    let tl = read hdl.tail.ptr in
    (* NS: Removing this rewrite results in a weird tactic left uninstantiated var error *)
    rewrite
      (ghost_pts_to hdl.tail.ghost half v)
      (ghost_pts_to hdl.tail.ghost half tl);
    let cell = Q.({ data = x; next = null} ) in
    let node = alloc cell in
    let enqueue_core #u ()
      : SteelAtomicT unit u observable
        (queue_invariant hdl.head hdl.tail `star`
          (ghost_pts_to hdl.tail.ghost half tl `star` pts_to node full cell))
        (fun _ -> queue_invariant hdl.head hdl.tail `star`
               ghost_pts_to hdl.tail.ghost half node)
      = let open FStar.Ghost in
        let h = open_exists () in
        let t = open_exists () in
        ghost_gather tl hdl.tail.ghost;
        rewrite
          (Q.queue h t)
          (Q.queue h tl);
        Q.enqueue tl node;
        ghost_write hdl.tail.ghost node;
        ghost_share #_ #_ hdl.tail.ghost;
        pack_queue_invariant _ _ _ _
    in
    with_invariant hdl.inv enqueue_core;
    write hdl.tail.ptr node;
    intro_exists
      _
      (fun n -> pts_to hdl.tail.ptr full_perm n `star`
             ghost_pts_to hdl.tail.ghost half n);
    Steel.SpinLock.release hdl.tail.lock

let maybe_ghost_pts_to #a (x:ghost_ref (Q.t a)) (hd:Q.t a) (o:option (Q.t a)) =
  match o with
  | None -> ghost_pts_to x half hd
  | Some next -> ghost_pts_to x half next `star` (h_exists (pts_to hd full_perm))

#push-options "--query_stats --log_queries"
let dequeue_core (#a:_) (#u:_) (hdl:t a) (hd:Q.t a) (_:unit)
  : SteelAtomicT (option (Q.t a)) u observable
    (queue_invariant hdl.head hdl.tail `star`
     ghost_pts_to hdl.head.ghost half hd)
    (fun o ->
      queue_invariant hdl.head hdl.tail `star`
      maybe_ghost_pts_to hdl.head.ghost hd o)
  = let h = open_exists () in
    let t = open_exists () in
    ghost_gather hd hdl.head.ghost;
    (* NS: I shouldn't need this, but somehow I still do *)
    rewrite (Q.queue h t) (Q.queue hd t);
    let o = Queue.dequeue hd in
    match o with
    | None ->
      rewrite (Q.dequeue_post _ _ _) (Q.queue hd t);
      ghost_share hdl.head.ghost;
      pack_queue_invariant _ _ hdl.head hdl.tail;
      rewrite
        (ghost_pts_to hdl.head.ghost _ _)
        (maybe_ghost_pts_to hdl.head.ghost hd o);
      o

    | Some p ->
      rewrite (Q.dequeue_post _ _ _) (Q.dequeue_post_success t hd p);
      let c = open_exists () in
      elim_pure ();
      intro_exists c (pts_to hd full_perm);
      ghost_write hdl.head.ghost p;
      ghost_share hdl.head.ghost;
      pack_queue_invariant _ _ hdl.head hdl.tail;
      rewrite
        (ghost_pts_to hdl.head.ghost _ _ `star` h_exists (pts_to hd full_perm))
        (maybe_ghost_pts_to hdl.head.ghost hd o);
      o

let dequeue (#a:_) (hdl:t a)
  : SteelT (option a) emp (fun _ -> emp)
  = Steel.SpinLock.acquire hdl.head.lock;
    let v = open_exists () in
    let hd = read hdl.head.ptr in
    let o = with_invariant hdl.inv (dequeue_core hdl hd) in
    match o with
    | None ->
      rewrite
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half hd);
      intro_exists _ (fun v -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      Steel.SpinLock.release hdl.head.lock;
      None

    | Some next ->
      rewrite
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half next `star` h_exists (pts_to hd full_perm));
      let c = open_exists () in
      write hdl.head.ptr next;
      intro_exists _ (fun v -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      Steel.SpinLock.release hdl.head.lock;
      let c = read hd in
      let v = c.Q.data in
      free hd;
      Some v
