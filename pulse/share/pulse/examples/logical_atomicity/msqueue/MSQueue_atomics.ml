(**
   Native test realization selected by MSQueue.Atomics-ocaml.fst.

   Queue cells extract to OCaml [Atomic.t] (Pulse.Lib.Atomic's atomic_box),
   and these primitives operate on them directly without locks: [read] is
   [Atomic.get], and [cas] is a value-comparing compare-and-set loop. F*
   UInt32 values are boxed, so the comparison is structural; the loop only
   retries when the cell was physically replaced by an equal value. This is
   handwritten code inside the runtime trust boundary, NOT verified OCaml.

   The global failure counter injects failures permitted by the weak-CAS
   contract. It tests abort/retry paths but makes no fairness guarantee.
*)

(** Remaining matching CAS calls to fail; updated atomically. *)
let failures_remaining = Atomic.make 0

(** Atomically consume one injected failure, if any remain. *)
let rec take_failure () =
  let n = Atomic.get failures_remaining in
  n > 0 && (Atomic.compare_and_set failures_remaining n (n - 1) || take_failure ())

(** Sequentially consistent load. *)
let read r = Atomic.get r

(** A mismatch fails without spending the injection budget. A matching call
   may fail spuriously; otherwise the write is a single physical CAS against
   the value just observed to be structurally equal to [expected]. *)
let rec cas r expected desired =
  let cur = Atomic.get r in
  if cur <> expected then false
  else if take_failure () then false
  else if Atomic.compare_and_set r cur desired then true
  else cas r expected desired

(** Replace the global budget for upcoming MATCHING CAS failures. Tests set
   this between batches, not as a per-thread scheduling guarantee. *)
let fail_next n =
  if n < 0 then invalid_arg "MSQueue_atomics.fail_next";
  Atomic.set failures_remaining n

(** Observe unconsumed failures so a test can detect an unexercised retry path. *)
let pending_failures () = Atomic.get failures_remaining
