(* The realization of Pulse.Lib.SpinLock.  Custard treats the module as
   realized and compiles none of it (doc/ref/custard.md section 128): its F*
   definition is built on Pulse.Lib.Primitives.cas, which is a *specification*
   -- a read followed by a write, atomic in Pulse's semantics and not atomic
   at all once it is OCaml -- so the compiled spin lock would lock nothing.

   A lock is a Mutex.t, which is what the legacy extraction pipeline also maps
   it to (pulse/src/extraction/ExtractPulseOCaml.fst).  The C realization is
   Pulse_Lib_SpinLock.c over pthread_mutex_t. *)

type lock = Mutex.t

let new_lock () : lock = Mutex.create ()

let acquire (l: lock) : unit = Mutex.lock l

let release (l: lock) : unit = Mutex.unlock l

(* The F* signature consumes the lock's invariant and returns nothing; OCaml
   mutexes are collected, so there is nothing to release. *)
let free (_: lock) : unit = ()
