(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.o
*)

module Steel.DisposableInvariant

open FStar.Ghost
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission

/// A library of disposable invariants (or "ghost locks"), which can be used for lock-free concurrency,
/// while allowing to reclaim the locked resource once the lock is not needed anymore.
/// This is analogous to Cancellable Invariants in Iris.

#push-options "--ide_id_info_off"

/// The abstract type of ghost locks. Only used for proof purposes, will be erased at extraction time
[@@ erasable]
val inv (p:vprop) : Type0

/// The name of a disposable invariant
val name (#p:_) (i:inv p) : Ghost.erased iname

/// Separation logic predicate stating that an invariant is currently active, and that we have permission [f]
/// on it. We can freely use the invariant as long as we have partial permission, but can only dispose of it
/// when we own the full permission.
/// The permission is annotated with the `smt_fallback` attribute, enabling automatic SMT rewritings on it
/// during frame inference
val active (#p:_) ([@@@ smt_fallback] f:perm) (_:inv p) : vprop

/// Creating a new invariant associated to vprop [p], as long as [p] was initially valid.
/// [p] is then removed from the context as it is now locked behind the invariant, and we
/// have full ownership on the newly minted invariant.
val new_inv (#u:_) (p:vprop)
  : SteelGhostT (inv p) u
    p
    (fun i -> active full_perm i)

/// Enables sharing an invariant between different threads.
val share (#p:vprop) (#f:perm) (#u:_) (i:inv p)
  : SteelGhostT unit u
    (active f i)
    (fun _ -> active (half_perm f) i `star` active (half_perm f) i)

/// Gathers an invariant that was previously shared.
val gather (#p:vprop) (#f0 #f1:perm) (#u:_) (i:inv p)
  : SteelGhostT unit u
    (active f0 i `star` active f1 i)
    (fun _ -> active (sum_perm f0 f1) i)

/// Some helpers to manipulate the set of currently opened invariants in the context.
let mem_inv (#p:vprop) (u:inames) (i:inv p) : GTot bool =
  Set.mem (reveal (name i)) (reveal u)

let add_inv (#p:vprop) (u:inames) (i:inv p) : inames =
  Set.union (Set.singleton (reveal (name i))) (reveal u)

/// If we have full ownership of the invariant, and it is not currently opened,
/// then we can dispose of it, and retrieve the locked resource
val dispose (#p:vprop) (#u:inames) (i:inv p{not (mem_inv u i)})
  : SteelGhostT unit u
    (active full_perm i)
    (fun _ -> p)

/// Lifting the standard with_invariant combinator to disposable invariants.
/// If invariant [i], locking vprop [p] is not currently opened, then an atomic
/// computation [f] can access the locked resource [p] as long as it restores it
/// upon termination.
val with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (#perm:_)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> SteelAtomicT a (add_inv opened_invariants i)
                                             (p `star` fp)
                                             (fun x -> p `star` fp' x))
  : SteelAtomicT a opened_invariants (active perm i `star` fp) (fun x -> active perm i `star` fp' x)

/// A variant of the above combinator for ghost computations.
val with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (#perm:_)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> SteelGhostT a (add_inv opened_invariants i)
                                               (p `star` fp)
                                               (fun x -> p `star` fp' x))
  : SteelGhostT a opened_invariants (active perm i `star` fp) (fun x -> active perm i `star` fp' x)
