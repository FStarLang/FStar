module LowStar.RST.Par

open LowStar.Resource
open LowStar.RST
open LowStar.Array
module RA = LowStar.RST.Array
module P = LowStar.Permissions

(*
   This module presents combinators to verify concurrent programs in Low*.
   It relies on the RST monad, and a memory model that includes permissions.
   A metatheoretic proof of these combinators is in progress in examples/lowstar_resources/Par{_Triple}.fst
*)


(* The par combinator executes two RST functions in parallel.
   The two functions need to have disjoint footprints: Their resources must be starred.
   Under these conditions, we get a pair, and the conjunction of the postconditions
   if the conjunction of the preconditions is initially satisfied.
   The definition of locations in the Heap with permissions model ensures that two different
   resources to the same address with read-only permission are disjoint, hence starred.
   This allows two threads to share a read-only resource.
   The model also prevents the existence of live pointers to the same address with write permission.
   *)
assume
val par (#in1 #in2:resource)
        (#a #b:Type)
        (#out1:a -> resource)
        (#out2:b -> resource)
        (#pre1:r_pre in1)
        (#pre2:r_pre in2)
        (#post1:r_post in1 a out1)
        (#post2:r_post in2 b out2)
        ($f1:unit -> RST a in1 out1 pre1 post1)
        ($f2:unit -> RST b in2 out2 pre2 post2)
        : RST (a & b)
              (in1 <*> in2)
              (fun p -> out1 (fst p) <*> out2 (snd p))
              (fun h -> pre1 h /\ pre2 h)
              (fun h0 (x, y) h1 -> post1 h0 x h1 /\ post2 h0 y h1)

(* We now model locks to permit the sharing of read/write resources. We currently model locks as values, which are therefore in scope of both threads when calling par.
   Locks have blocking semantics: Preconditions on acquire are minimal, but the freedom of the lock is checked at runtime. A program will halt until the required lock
   becomes available.
   This model should prevent data races, but is inadequate to prove absence of deadlocks (for instance, we can try to acquire twice the same lock in a thread)
   TODO: Investigate using locks as special resources
   TODO: Enhance the metatheory to model locks
*)

// We take a lock on an array. TODO: Should it be on an array resource instead?
// The lock has a predicate on the resource view associated.
// This is all we know about the locked memory contents.
// It must be proven correct at lock creation, and each time a lock is released
assume
val lock (#a:Type) (b:array a) : Type
// Locks could possibly be implemented as exactly the associated predicate.
// We have to ensure that the definition is abstract to prevent users to
// create them without using the creation functions
assume
val get_lock_pred (#a:Type) (#b:array a) (l:lock b) : Seq.seq a -> Type

(* We are only allowed to take a lock on a resource with write permission.
   We could also remove this restriction and store the permission in the lock, but
   we probably don't need locks on shareable, read only permissions *)
assume
val new_lock (#a:Type) (b:array a) (pred:Seq.seq a -> Type)
  : RST (lock b)
        (RA.array_resource b) (fun _ -> empty_resource)
        (fun h ->
          pred (sel (RA.array_view b) h).RA.s /\
          P.allows_write (Ghost.reveal (sel (RA.array_view b) h).RA.p))
        (fun _ l _ -> get_lock_pred l == pred)

/// This model could allow a thread to acquire a lock, and create a new lock
/// with a different predicate (assuming this predicate is now satisfied)
/// This could be problematic if another thread acquires the initial lock and only proves
/// the preservation of the original predicate
/// Nevertheless, this behaviour is prevented by the dynamic semantics: If thread A acquires the lock
/// and creates a new one with a new predicate, thread B cannot acquire the same lock until A releases it with the original predicate.
/// TODO: We should be especially careful modeling this and proving this property

(* When we acquire a lock, the locked resource is now in context.
   We only know about its contents what was stored in the lock
   *)
assume
val acquire (#a:Type) (b:array a) (l:lock b)
  : RST unit
        (empty_resource)
        (fun _ -> RA.array_resource b)
        (fun _ -> True)
        (fun _ _ h1 ->
          (get_lock_pred l) (sel (RA.array_view b) h1).RA.s /\
          P.allows_write (Ghost.reveal (sel (RA.array_view b) h1).RA.p))

(* Release is similar to new_lock, without the new value creation *)
assume
val release (#a:Type) (b:array a) (l:lock b)
  : RST unit
        (RA.array_resource b)
        (fun _ -> empty_resource)
        (fun h ->
          (get_lock_pred l) (sel (RA.array_view b) h).RA.s /\
          P.allows_write (Ghost.reveal (sel (RA.array_view b) h).RA.p))
        (fun _ _ _ -> True)
