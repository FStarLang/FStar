module Test.Par.Locks2

module P = LowStar.Permissions
module A = LowStar.RST.Array
module HST = FStar.HyperStack.ST
open LowStar.RST.Par2
open LowStar.Array

open LowStar.Resource
open LowStar.RST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=100"

let test_create_lock (b:array UInt32.t) : RST 
  (lock (A.array_resource b) (fun s -> s.A.s `Seq.equal` Seq.create 1 1ul /\ P.allows_write (Ghost.reveal s.A.p)))
  (A.array_resource b)
  (fun _ -> empty_resource)
  (fun h -> vlength b = 1 /\ 
         P.allows_write (Ghost.reveal (sel (A.array_view b) h).A.p) /\
         (sel (A.array_view b) h).A.s == Seq.create 1 1ul
         )
  (fun _ l _ -> True)
  =
  let l = new_lock (A.array_resource b) (fun s -> s.A.s `Seq.equal` Seq.create 1 1ul /\ P.allows_write (Ghost.reveal s.A.p)) in
  acquire l;
  let x = A.index b 0ul in
  assert (UInt32.v x == 1);
  A.upd b 0ul 1ul;
  release l;
  l

/// Having the lock indiced by the predicate forces a syntactic equality. We cannot use predicate extensionality anymore
let test_create_lock2 (b:array UInt32.t) : RST 
  (lock (A.array_resource b) (fun s -> Seq.index s.A.s 0 == 1ul /\ P.allows_write (Ghost.reveal s.A.p)))
  (A.array_resource b)
  (fun _ -> empty_resource)
  (fun h -> vlength b = 1 /\ 
         P.allows_write (Ghost.reveal (sel (A.array_view b) h).A.p) /\
         (sel (A.array_view b) h).A.s == Seq.create 1 1ul
         )
  (fun _ l _ -> True)
  =
  let l = new_lock (A.array_resource b) (fun s -> s.A.s `Seq.equal` Seq.create 1 1ul /\ P.allows_write (Ghost.reveal s.A.p)) in
  acquire l;
  let x = A.index b 0ul in
  assert (UInt32.v x == 1);
  A.upd b 0ul 1ul;
  release l;
  l
