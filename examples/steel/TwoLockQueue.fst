module TwoLockQueue

open FStar.Ghost
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
open  Steel.SpinLock
module L = FStar.List.Tot
module U = Steel.Utils
module Q = Queue

#push-options "--ide_id_info_off"

let _: squash (forall p q. p `equiv` q <==> hp_of p `Steel.Memory.equiv` hp_of q) =
  Classical.forall_intro_2 reveal_equiv



[@@__reduce__]
let full = full_perm
[@@__reduce__]
let half = half_perm full
let fst x = fst x
let snd x = snd x

let ghost_gather (#a:Type) (#u:_)
                 (#p0 #p1:perm) (#p:perm{p == sum_perm p0 p1})
                 (x0 #x1:erased a)
                 (r:ghost_ref a)
  : SteelGhost unit u
    (ghost_pts_to r p0 x0 `star`
     ghost_pts_to r p1 x1)
    (fun _ -> ghost_pts_to r p x0)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> x0 == x1)
  = let _ = ghost_gather_pt #a #u #p0 #p1 r in ()

let rewrite #u (p q:vprop)
  : SteelGhost unit u p (fun _ -> q)
    (requires fun _ -> p `equiv` q)
    (ensures fun _ _ _ -> True)
  = rewrite_slprop p q (fun _ -> reveal_equiv p q)

let elim_pure (#p:prop) #u ()
  : SteelGhost unit u
                (pure p) (fun _ -> emp)
                (requires fun _ -> True)
                (ensures fun _ _ _ -> p)
  = let _ = Steel.Effect.Atomic.elim_pure p in ()

let open_exists (#a:Type) (#opened_invariants:_) (#p:Ghost.erased a -> vprop) (_:unit)
  : SteelGhostT (Ghost.erased a) opened_invariants
                 (h_exists p) p
  = let v : erased (erased a)  = witness_exists () in
    reveal v

[@@__reduce__]
let lock_inv #a (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t a)) =
    h_exists (fun (v:erased (Q.t a)) ->
      pts_to ptr full v `star`
      ghost_pts_to ghost half v)

let intro_lock_inv #a #u (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t
a))
  : SteelGhostT unit u
    (h_exists (fun v ->
      pts_to ptr full v `star`
      ghost_pts_to ghost half v))
    (fun _ -> lock_inv ptr ghost)
  = rewrite_slprop _ _ (fun _ -> ())

noeq
type q_ptr (a:Type) = {
  ptr : ref (Q.t a);
  ghost: ghost_ref (Q.t a);
  lock: lock (lock_inv ptr ghost);
}

let queue_invariant (#a:_) ([@@@smt_fallback]head:q_ptr a) ([@@@smt_fallback] tail:q_ptr a) =
  h_exists (fun h ->
  h_exists (fun t ->
    ghost_pts_to head.ghost half h `star`
    ghost_pts_to tail.ghost half t `star`
    Q.queue h t))

let pack_queue_invariant (#a:_) (#u:_) (x:erased (Q.t a)) (y:erased (Q.t a)) (head tail:q_ptr a)
 : SteelGhostT unit u
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
      = let ptr = alloc_pt q in
        let ghost = ghost_alloc_pt q in
        ghost_share_pt ghost;
        intro_exists _ (fun q -> pts_to ptr full q `star` ghost_pts_to ghost half q);
        let lock = Steel.SpinLock.new_lock _ in
        { ptr; ghost; lock}
    in
    let hd = Q.new_queue x in
    let head = new_qptr hd in
    let tail = new_qptr hd in
    pack_queue_invariant _ _ head tail;
    let inv = new_invariant _ in
    return ({ head; tail; inv })

#restart-solver

let enqueue (#a:_) (hdl:t a) (x:a)
  : SteelT unit emp (fun _ -> emp)
  = Steel.SpinLock.acquire hdl.tail.lock;
    let cell = Q.({ data = x; next = null} ) in
    let v:erased (Q.t a) = open_exists () in
    let tl = read_pt hdl.tail.ptr in
    let node = alloc_pt cell in
    let enqueue_core #u ()
      : SteelAtomicT unit u
        (queue_invariant hdl.head hdl.tail `star`
          (ghost_pts_to hdl.tail.ghost half tl `star` pts_to node full cell))
        (fun _ -> queue_invariant hdl.head hdl.tail `star`
               ghost_pts_to hdl.tail.ghost half node)
      = let open FStar.Ghost in
        let h = open_exists () in
        let t = open_exists () in

        ghost_gather tl hdl.tail.ghost;
        Q.enqueue tl node;

        ghost_write_pt hdl.tail.ghost node;

        ghost_share_pt #_ #_ hdl.tail.ghost;
        pack_queue_invariant _ _ hdl.head hdl.tail;
        return ()
    in
    let r1 = with_invariant hdl.inv enqueue_core in
    let r2 = write_pt hdl.tail.ptr node in
    let r3 = intro_exists
      _
      (fun (n:erased (Q.t a)) -> pts_to hdl.tail.ptr full_perm n `star`
             ghost_pts_to hdl.tail.ghost half n) in
    Steel.SpinLock.release hdl.tail.lock

let maybe_ghost_pts_to #a (x:ghost_ref (Q.t a)) ([@@@ smt_fallback] hd:Q.t a) (o:option (Q.t a)) =
  match o with
  | None -> ghost_pts_to x half hd
  | Some next -> ghost_pts_to x half next `star` (h_exists (pts_to hd full_perm))

let dequeue_core (#a:_) (#u:_) (hdl:t a) (hd:Q.t a) (_:unit)
  : SteelAtomicT (option (Q.t a)) u
    (queue_invariant hdl.head hdl.tail `star`
     ghost_pts_to hdl.head.ghost half hd)
    (fun o ->
      queue_invariant hdl.head hdl.tail `star`
      maybe_ghost_pts_to hdl.head.ghost hd o)
  = let h = open_exists () in
    let t = open_exists () in
    ghost_gather hd hdl.head.ghost;

    let o = Queue.dequeue hd in
    match o with
    | None ->
      rewrite (Q.dequeue_post _ _ _) (Q.queue hd t);
      ghost_share_pt hdl.head.ghost;
      pack_queue_invariant hd t hdl.head hdl.tail;
      rewrite
        (ghost_pts_to hdl.head.ghost _ _)
        (maybe_ghost_pts_to _ _ _);
      return o

    | Some p ->
      rewrite (Q.dequeue_post _ _ _) (Q.dequeue_post_success _ _ _);
      let c = open_exists () in
      elim_pure ();
      intro_exists c (pts_to hd full_perm);
      ghost_write_pt hdl.head.ghost p;
      ghost_share_pt hdl.head.ghost;
      pack_queue_invariant _ _ hdl.head hdl.tail;
      assert (maybe_ghost_pts_to hdl.head.ghost hd (Some p) == ghost_pts_to hdl.head.ghost half p `star` h_exists (pts_to hd full_perm)) by (FStar.Tactics.norm [delta; iota; zeta]);
      rewrite
        (ghost_pts_to hdl.head.ghost half p `star` h_exists (pts_to hd full_perm))
        (maybe_ghost_pts_to hdl.head.ghost hd o);
      return o

let dequeue (#a:_) (hdl:t a)
  : SteelT (option a) emp (fun _ -> emp)
  = Steel.SpinLock.acquire hdl.head.lock;
    let v = open_exists () in
    let hd = read_pt hdl.head.ptr in
    let o = with_invariant hdl.inv (dequeue_core hdl hd) in
    match o with
    | None ->
      rewrite_slprop
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half hd)
        (fun _ -> ());
      intro_exists _ (fun v -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      Steel.SpinLock.release hdl.head.lock;
      None

    | Some next ->
      let open FStar.Tactics in
      assert (maybe_ghost_pts_to hdl.head.ghost hd (Some next) == ghost_pts_to hdl.head.ghost half next `star` h_exists (pts_to hd full_perm)) by (norm [delta; iota; zeta]);
      rewrite_slprop
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half next `star` h_exists (pts_to hd full_perm))
        (fun _ -> ());
      let c = open_exists () in
      write_pt hdl.head.ptr next;
      intro_exists _ (fun v -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      Steel.SpinLock.release hdl.head.lock;
      let c = read_pt hd in
      let v = c.Q.data in
      free_pt hd;
      Some v
