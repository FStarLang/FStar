module Test.Par.Locks

module P = LowStar.Permissions
module A = Steel.Array
module HST = FStar.HyperStack.ST
open Steel.Par
open Steel.RST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=100"

let test_create_lock (b:A.array UInt32.t) : RST (lock (A.array_resource b))
  (A.array_resource b)
  (fun _ -> empty_resource)
  (fun old -> A.vlength b = 1 /\
         P.allows_write (A.get_rperm b old) /\
         A.as_rseq b old == Seq.create 1 1ul
         )
  (fun _ l _ ->
    (forall s. get_lock_pred l s <==> (Seq.index s.A.s 0 == 1ul /\ P.allows_write (Ghost.reveal s.A.p)) ) )
  =
  let l = new_lock (A.array_resource b) (fun s -> s.A.s `Seq.equal` Seq.create 1 1ul /\ P.allows_write (Ghost.reveal s.A.p)) in
  acquire l;
  let x = A.index b 0ul in
  assert (UInt32.v x == 1);
  A.upd b 0ul 1ul;
  release l;
  l

let test_create_lock2 (b:A.array UInt32.t) : RST (lock (A.array_resource b))
  (A.array_resource b)
  (fun _ -> empty_resource)
  (fun old -> A.vlength b = 2 /\
         P.allows_write (A.get_rperm b old)
         )
  (fun _ l _ ->
    (forall s. get_lock_pred l s <==> Seq.index s.A.s 0 == 1ul /\ P.allows_write (Ghost.reveal s.A.p)) )
  =
  A.upd b 0ul 1ul;
  A.upd b 1ul 1ul;
  let l = new_lock (A.array_resource b) (fun s -> Seq.index s.A.s 0 == 1ul /\ P.allows_write (Ghost.reveal s.A.p)) in
  acquire l;
  let x = A.index b 0ul in
  let y = A.index b 1ul in
  assert (UInt32.v x == 1);
  // assert (UInt32.v y == 1);
  // This assertion is not provable, as expected:
  // The invariant in the lock doesn't provide talk about the second index of b,
  // so any information about it is lost once the lock is created
  release l;
  l


let basic_locked_update (b:A.array UInt32.t) (l:lock (A.array_resource b)) : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  // When we pass a lock, we need to express something about the predicate associated to satisfy the precondition of release
  // In this case, the lock is almost trivial, but needs to specify the write permission
  (fun old -> A.vlength b = 1 /\ (forall s. get_lock_pred l s <==> P.allows_write (Ghost.reveal s.A.p)))
  (fun _ _ _ -> True)
  =
  acquire l;
  let x = A.index b 0ul in
  A.upd b 0ul (x `UInt32.add_mod` 1ul);
  release l

let test_shared_lock () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun old -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 1ul 1ul in
  let l = new_lock (A.array_resource b) (fun s -> P.allows_write (Ghost.reveal s.A.p)) in
  // Frame is here needed to unify empty_resource with empty <*> empty
  // Unclear why inlining the framed function does not work and points to prims (112- 150)
  let f = fun () -> par (fun () -> basic_locked_update b l) (fun () -> basic_locked_update b l) in
  let _ = rst_frame (empty_resource) (fun _ -> empty_resource) f in
  acquire l;
  let x = A.index b 0ul in
  // Here, we do not know anything about the contents of b since no invariant is associated to the lock
  release l


let locked_update2 (b:A.array UInt32.t) (l:lock (A.array_resource b)) (v:UInt32.t) : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  // When we pass a lock, we need to express something about the predicate associated to satisfy the precondition of release
  (fun old -> A.vlength b = 2 /\ (forall s. (
    P.allows_write (Ghost.reveal s.A.p) /\
    UInt32.v (Seq.index s.A.s 0) >= UInt32.v (Seq.index s.A.s 1)) <==> get_lock_pred l s))
  (fun _ _ _ -> True)
  =
  acquire l;
  let x = A.index b 0ul in
  if x `UInt32.gte` v then
    A.upd b 1ul v
  else ();
  release l

let test_shared_lock2 () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun old -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 1ul 2ul in
  let l = new_lock (A.array_resource b) (fun s -> UInt32.v (Seq.index s.A.s 0) >= UInt32.v (Seq.index s.A.s 1) /\ P.allows_write (Ghost.reveal s.A.p)) in
  // Frame is here needed to unify empty_resource with empty <*> empty
  // Unclear why inlining the framed function does not work and points to prims (112- 150)
  let f = fun () -> par (fun () -> locked_update2 b l 5ul) (fun () -> locked_update2 b l 10ul) in
  let _ = rst_frame (empty_resource) (fun _ -> empty_resource) f in
  acquire l;
  let x = A.index b 0ul in
  let y = A.index b 1ul in
  // We only know what happened is given by the lock invariant here
  assert (UInt32.v x >= UInt32.v x);
  release l
