(**
   Native test realization selected by MSQueue.Atomics-ocaml.fst.

   A single mutex serializes each read/CAS on ordinary OCaml refs. Queue
   operations still interleave between primitive calls; there is no lock
   spanning an entire enqueue/dequeue. This is a linearizable primitive
   realization for testing, NOT a lock-free backend or verified OCaml code.
   The F* wrappers prove contracts against Pulse's primitive model; matching
   those contracts here is part of the handwritten-runtime trust boundary.

   The global failure counter injects failures permitted by the weak-CAS
   contract. It tests abort/retry paths but makes no fairness guarantee.
*)

(** Shared by all queue instances so every realized primitive is indivisible. *)
let lock = Mutex.create ()
(** Remaining matching CAS calls to fail; accessed only under lock. *)
let failures_remaining = ref 0

(** Run one primitive and release the mutex even if its body raises. *)
let synchronized f =
  Mutex.lock lock;
  Fun.protect ~finally:(fun () -> Mutex.unlock lock) f

(** Load at a point serialized with all other realized reads and CAS calls. *)
let read r = synchronized (fun () -> !r)

(** A mismatch fails without spending the injection budget. A matching call
   may fail spuriously; otherwise comparison and write occur under one lock. *)
let cas r expected desired =
  synchronized (fun () ->
    if !r <> expected then false
    else if !failures_remaining > 0 then (
      decr failures_remaining;
      false)
    else (
      r := desired;
      true))

(** Replace the global budget for upcoming MATCHING CAS failures. Tests set
   this between batches, not as a per-thread scheduling guarantee. *)
let fail_next n =
  if n < 0 then invalid_arg "MSQueue_atomics.fail_next";
  synchronized (fun () -> failures_remaining := n)

(** Observe unconsumed failures so a test can detect an unexercised retry path. *)
let pending_failures () = synchronized (fun () -> !failures_remaining)
