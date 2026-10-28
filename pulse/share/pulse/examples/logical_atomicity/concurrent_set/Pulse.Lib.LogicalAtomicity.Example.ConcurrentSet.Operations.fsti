module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Operations
#lang-pulse

(**
Public logically atomic set interface.

An AU supplies the abstract state at commitment, not at function entry.
The returned boolean is exact; all other memberships are unchanged. The
continuation may transfer private ghost or physical ownership. Clients need
neither the list layout nor the implementation's choice of linearization point.

Keys lie in the fixed universe 1..capacity. Zero and capacity+1 are sentinels.
Operations may block indefinitely acquiring node locks. No checker changes,
prophecies, or general sendability assumption for AUs are used.
*)

open Pulse.Lib.Pervasives
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model
module Q = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State
module A = Pulse.Lib.LogicalAtomicity.Atomic

(** Operation-visible model ownership, usually lent by a client invariant. *)
let alpha (q:Q.set) (s:Q.contents q.Q.cells) = Q.model q s
(** Add installs k, remove clears k, and contains leaves the set unchanged.
Add returns previous absence; remove and contains return previous membership. *)
let beta (q:Q.set) (op:H.operation) (k:Q.key q) (s:Q.contents q.Q.cells) (r:bool) =
  Q.model q (H.after op s k) ** pure (r == H.answer op s k)
(** Client-chosen postcondition, mask, and per-opening credit cost. *)
let update q op k inner credits (phi:bool -> slprop) =
  A.atomic_update emp_inames inner credits (alpha q) (beta q op k) (fun _ r -> phi r)

divergent fn add (q:Q.set) (k:Q.key q)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q
  requires update q H.Add k inner credits phi
  returns r:bool
  ensures phi r

divergent fn remove (q:Q.set) (k:Q.key q)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q
  requires update q H.Remove k inner credits phi
  returns r:bool
  ensures phi r

divergent fn contains (q:Q.set) (k:Q.key q)
  (inner:inames { not (mem_inv inner q.Q.name) }) credits phi
  preserves Q.is_set q
  requires update q H.Contains k inner credits phi
  returns r:bool
  ensures phi r
