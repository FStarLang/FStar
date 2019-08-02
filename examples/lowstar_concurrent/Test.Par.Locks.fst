module Test.Par.Locks

module P = LowStar.Permissions
module A = LowStar.RST.Array
module HST = FStar.HyperStack.ST
open LowStar.RST.Par
open LowStar.Array

open LowStar.Resource
open LowStar.RST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=100"

let test_create_lock (b:array UInt32.t) : RST (lock b)
  (A.array_resource b)
  (fun _ -> empty_resource)
  (fun h -> vlength b = 1 /\ 
         P.allows_write (Ghost.reveal (sel (A.array_view b) h).A.p) /\
         (sel (A.array_view b) h).A.s == Seq.create 1 1ul
         )
  (fun _ l _ -> 
    (forall s. get_lock_pred l s <==> Seq.index s 0 == 1ul) )
  =
  let l = new_lock b (fun s -> s `Seq.equal` Seq.create 1 1ul) in
  acquire b l;
  let x = A.index b 0ul in
  assert (UInt32.v x == 1);
  release b l;
  l

let test_create_lock2 (b:array UInt32.t) : RST (lock b)
  (A.array_resource b)
  (fun _ -> empty_resource)
  (fun h -> vlength b = 2 /\ 
         P.allows_write (Ghost.reveal (sel (A.array_view b) h).A.p)
         )
  (fun _ l _ -> 
    (forall s. get_lock_pred l s <==> Seq.index s 0 == 1ul) )
  =
  A.upd b 0ul 1ul;
  A.upd b 1ul 1ul;
  let l = new_lock b (fun s -> Seq.index s 0 == 1ul) in
  acquire b l;
  let x = A.index b 0ul in
  let y = A.index b 1ul in
  assert (UInt32.v x == 1);
  // assert (UInt32.v y == 1);
  // This assertion is not provable, as expected: 
  // The invariant in the lock doesn't provide talk about the second index of b, 
  // so any information about it is lost once the lock is created
  release b l;
  l


let basic_locked_update (b:array UInt32.t) (l:lock b) : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  // When we pass a lock, we need to express something about the predicate associated to satisfy the precondition of release
  // In this case, the lock is assumed trivial
  (fun h -> vlength b = 1 /\ (forall s. get_lock_pred l s))
  (fun _ _ _ -> True)
  =
  acquire b l;
  let x = A.index b 0ul in
  A.upd b 0ul (x `UInt32.add_mod` 1ul);
  release b l

let test_shared_lock () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun h -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 1ul 1ul in
  let l = new_lock b (fun _ -> True) in
  // Frame is here needed to unify empty_resource with empty <*> empty
  // Unclear why inlining the framed function does not work and points to prims (112- 150)
  let f = fun () -> par (fun () -> basic_locked_update b l) (fun () -> basic_locked_update b l) in
  let _ = rst_frame (empty_resource) (fun _ -> empty_resource) f in
  acquire b l;
  let x = A.index b 0ul in
  // Here, we do not know anything about the contents of b since no invariant is associated to the lock
  release b l


let locked_update2 (b:array UInt32.t) (l:lock b) (v:UInt32.t) : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  // When we pass a lock, we need to express something about the predicate associated to satisfy the precondition of release
  // If we do not care about logical predicates regarding contents when acquiring the lock, an implication is enough
  (fun h -> vlength b = 2 /\ (forall s. UInt32.v (Seq.index s 0) >= UInt32.v (Seq.index s 1) ==> get_lock_pred l s))
  (fun _ _ _ -> True)
  =
  acquire b l;
  let x = A.index b 0ul in
  if x `UInt32.gte` v then
    A.upd b 1ul v
  else ();
  release b l

let test_shared_lock2 () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun h -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 1ul 2ul in
  let l = new_lock b (fun s -> UInt32.v (Seq.index s 0) >= UInt32.v (Seq.index s 1)) in
  // Frame is here needed to unify empty_resource with empty <*> empty
  // Unclear why inlining the framed function does not work and points to prims (112- 150)
  let f = fun () -> par (fun () -> locked_update2 b l 5ul) (fun () -> locked_update2 b l 10ul) in
  let _ = rst_frame (empty_resource) (fun _ -> empty_resource) f in
  acquire b l;
  let x = A.index b 0ul in
  let y = A.index b 1ul in
  // We only know what happened is given by the lock invariant here
  assert (UInt32.v x >= UInt32.v x);
  release b l
