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

/// This module provides an implementation of Michael and Scott's two lock queue, using the
/// abstract interface for queues provided in Queue.fsti.
/// This implementation allows an enqueue and a dequeue operation to safely operate in parallel.
/// There is a lock associated to both the enqueuer and the dequeuer, which guards each of those operation,
/// ensuring that at most one enqueue (resp. dequeue) is happening at any time
/// We only prove that this implementation is memory safe, and do not prove the functional correctness of the concurrent queue

#push-options "--ide_id_info_off"

/// Adding the definition of the vprop equivalence to the context, for proof purposes
let _: squash (forall p q. p `equiv` q <==> hp_of p `Steel.Memory.equiv` hp_of q) =
  Classical.forall_intro_2 reveal_equiv


(* Some wrappers to reduce clutter in the code *)
[@@__reduce__]
let full = full_perm
[@@__reduce__]
let half = half_perm full

(* Wrappers around fst and snd to avoid overnormalization.
   TODO: The frame inference tactic should not normalize fst and snd *)

let fst x = fst x
let snd x = snd x

(* Some wrappers around Steel functions which are easier to use inside this module *)

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

(*** Queue invariant ***)

/// The invariant associated to the lock. Basically a variant of the
/// Owicki-Gries invariant, but applied to queues
[@@__reduce__]
let lock_inv #a (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t a)) =
    h_exists (fun (v:erased (Q.t a)) ->
      pts_to ptr full v `star`
      ghost_pts_to ghost half v)

let intro_lock_inv #a #u (ptr:ref (Q.t a)) (ghost:ghost_ref (Q.t a))
  : SteelGhostT unit u
    (h_exists (fun v -> pts_to ptr full v `star` ghost_pts_to ghost half v))
    (fun _ -> lock_inv ptr ghost)
  = rewrite_slprop _ _ (fun _ -> assert_norm (lock_inv ptr ghost == h_exists (fun v -> pts_to ptr full v `star` ghost_pts_to ghost half v)))

/// The type of a queue pointer.
/// Contains the concrete pointer [ptr], the pointer to ghost state [ghost],
/// and a lock [lock] protecting the invariant relating the concrete and ghost states
noeq
type q_ptr (a:Type) = {
  ptr : ref (Q.t a);
  ghost: ghost_ref (Q.t a);
  lock: lock (lock_inv ptr ghost);
}

/// The global queue invariant, which will be shared by the enqueuer and the dequeuer.
/// Again, inspired by the Owicki-Gries counter: It contains half the permission for the ghost
/// state of the enqueuer and dequeuer, while ensuring that the concrete queue always remains
/// a valid queue
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

/// The type of a queue. It contains a head and tail pointers, each with their own ghost state,
/// as well as the global queue invariant [inv]. Note that compared to the locks in the head and tail
/// pointers with type `q_ptr`, since invariant is a true Steel invariant, only accessible inside
/// atomic computations
noeq
type t (a:Type0) = {
  head : q_ptr a;
  tail : q_ptr a;
  inv : inv (queue_invariant head tail)
}

/// Creating a new queue.
let new_queue (#a:_) (x:a)
  : SteelT (t a) emp (fun _ -> emp)
  = let new_qptr (#a:_) (q:Q.t a)
      : SteelT (q_ptr a) emp (fun qp -> ghost_pts_to qp.ghost half q)
      = // Allocates the concrete pointer.
        let ptr = alloc_pt q in
        // Allocates the ghost state, and sets the corresponding lock invariant
        let ghost = ghost_alloc_pt q in
        ghost_share_pt ghost;
        intro_exists _ (fun q -> pts_to ptr full q `star` ghost_pts_to ghost half q);
        let lock = Steel.SpinLock.new_lock _ in
        { ptr; ghost; lock}
    in
    // Creating a concrete queue
    let hd = Q.new_queue x in
    // Creating the head and queue pointers
    let head = new_qptr hd in
    let tail = new_qptr hd in
    // Creating the global queue invariant
    pack_queue_invariant _ _ head tail;
    let inv = new_invariant _ in
    // Packing the different components to return a queue, as defined in type `t`
    return ({ head; tail; inv })

#restart-solver

/// Enqueues element [x] in the queue [hdl]
let enqueue (#a:_) (hdl:t a) (x:a)
  : SteelT unit emp (fun _ -> emp)
  = // Blocks until it can acquire the tail lock corresponding to the enqueuer
    Steel.SpinLock.acquire hdl.tail.lock;
    let cell = Q.({ data = x; next = null} ) in
    let v:erased (Q.t a) = open_exists () in
    let tl = read_pt hdl.tail.ptr in
    // Creates a new cell for the enqueued element
    let node = alloc_pt cell in
    // Core, atomic enqueue function, calling the concrete enqueue function while also
    // modifying ghost state to preserve the invariants
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
    // Actually executing the atomic enqueue operation while preserving the global queue invariant
    let r1 = with_invariant hdl.inv enqueue_core in
    // Updates the queue tail pointer
    let r2 = write_pt hdl.tail.ptr node in
    // Updates the queue tail ghost state
    let r3 = intro_exists
      _
      (fun (n:erased (Q.t a)) -> pts_to hdl.tail.ptr full_perm n `star`
             ghost_pts_to hdl.tail.ghost half n) in
    // Releases the tail lock corresponding to the enqueuer
    Steel.SpinLock.release hdl.tail.lock

let maybe_ghost_pts_to #a (x:ghost_ref (Q.t a)) ([@@@ smt_fallback] hd:Q.t a) (o:option (Q.t a)) =
  match o with
  | None -> ghost_pts_to x half hd
  | Some next -> ghost_pts_to x half next `star` (h_exists (pts_to hd full_perm))

/// Actual atomic dequeue operation, preserving the global queue invariant.
let dequeue_core (#a:_) (#u:_) (hdl:t a) (hd:Q.t a) (_:unit)
  : SteelAtomicT (option (Q.t a)) u
    (queue_invariant hdl.head hdl.tail `star`
     ghost_pts_to hdl.head.ghost half hd)
    (fun o ->
      queue_invariant hdl.head hdl.tail `star`
      maybe_ghost_pts_to hdl.head.ghost hd o)
  =
    let h = open_exists () in
    let t = open_exists () in
    ghost_gather hd hdl.head.ghost;

    // Attempts a concrete dequeue
    let o = Queue.dequeue hd in
    match o with
    | None ->
      // The list was empty, dequeue failed. We repack the invariant
      rewrite (Q.dequeue_post _ _ _) (Q.queue hd t);
      ghost_share_pt hdl.head.ghost;
      pack_queue_invariant hd t hdl.head hdl.tail;
      rewrite
        (ghost_pts_to hdl.head.ghost _ _)
        (maybe_ghost_pts_to _ _ _);
      return o

    | Some p ->
      // dequeue succeeded, and returned element p
      rewrite (Q.dequeue_post _ _ _) (Q.dequeue_post_success _ _ _);
      let c = open_exists () in
      elim_pure ();
      intro_exists c (pts_to hd full_perm);
      // Updates the head ghost state
      ghost_write_pt hdl.head.ghost p;
      ghost_share_pt hdl.head.ghost;
      // Repack the global queue invariant
      pack_queue_invariant _ _ hdl.head hdl.tail;
      assert (maybe_ghost_pts_to hdl.head.ghost hd (Some p) == ghost_pts_to hdl.head.ghost half p `star` h_exists (pts_to hd full_perm)) by (FStar.Tactics.norm [delta; iota; zeta]);
      rewrite
        (ghost_pts_to hdl.head.ghost half p `star` h_exists (pts_to hd full_perm))
        (maybe_ghost_pts_to hdl.head.ghost hd o);
      return o

/// Attempts to dequeue an element from the queue.
let dequeue (#a:_) (hdl:t a)
  : SteelT (option a) emp (fun _ -> emp)
  = // Blocks until it can acquire the head lock, corresponding to the dequeuer
    Steel.SpinLock.acquire hdl.head.lock;
    let v = open_exists () in
    let hd = read_pt hdl.head.ptr in
    // Executes the atomic dequeue, preserving the global queue invariant
    let o = with_invariant hdl.inv (dequeue_core hdl hd) in
    match o with
    | None ->
      // Dequeue failed, restore the dequeuer's ghost state
      rewrite_slprop
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half hd)
        (fun _ -> ());
      intro_exists _ (fun v -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      // Finally release the dequeuer lock
      Steel.SpinLock.release hdl.head.lock;
      None

    | Some next ->
      // Dequeue succeeded
      let open FStar.Tactics in
      assert (maybe_ghost_pts_to hdl.head.ghost hd (Some next) == ghost_pts_to hdl.head.ghost half next `star` h_exists (pts_to hd full_perm)) by (norm [delta; iota; zeta]);
      rewrite_slprop
        (maybe_ghost_pts_to hdl.head.ghost hd o)
        (ghost_pts_to hdl.head.ghost half next `star` h_exists (pts_to hd full_perm))
        (fun _ -> ());
      let c = open_exists () in
      // Update the concrete head pointer to the new head of the queue
      write_pt hdl.head.ptr next;
      // Repack the dequeuer lock invariant
      intro_exists _ (fun v -> pts_to hdl.head.ptr full v `star` ghost_pts_to hdl.head.ghost half v);
      // Release the dequeuer lock
      Steel.SpinLock.release hdl.head.lock;
      // Free the now unneeded pointer to the next element in the dequeued cell
      let c = read_pt hd in
      let v = c.Q.data in
      free_pt hd;
      Some v
