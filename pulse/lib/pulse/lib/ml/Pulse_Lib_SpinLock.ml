(* The realization of Pulse.Lib.SpinLock.  Custard treats the module as
   realized and compiles none of it (doc/ref/custard.md section 128): its F*
   model, Pulse.Lib.SpinLock-model.fst, is a busy-waiting loop over
   Pulse.Lib.Atomic, and a blocking mutex is the better runtime lock.

   A lock is a Mutex.t.  The C realization is
   Pulse_Lib_SpinLock.c over pthread_mutex_t. *)

type lock = Mutex.t

let new_lock () : lock = Mutex.create ()

let acquire (l: lock) : unit = Mutex.lock l

let release (l: lock) : unit = Mutex.unlock l

(* The F* signature consumes the lock's invariant and returns nothing; OCaml
   mutexes are collected, so there is nothing to release. *)
let free (_: lock) : unit = ()
