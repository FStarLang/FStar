(* Test-local realization of Pulse.Lib.Primitives. A single mutex serializes
   each primitive, not a whole logical-atomic operation. This is a handwritten
   runtime trust boundary, not a lock-free backend or the sequential F* model. *)
let lock = Mutex.create ()

let synchronized f =
  Mutex.lock lock;
  Fun.protect ~finally:(fun () -> Mutex.unlock lock) f

let read_atomic (r : FStar_UInt32.t ref) =
  synchronized (fun () -> !r)

let write_atomic (r : FStar_UInt32.t ref) x =
  synchronized (fun () -> r := x)

let cas (r : FStar_UInt32.t ref) expected desired =
  synchronized (fun () ->
    if !r <> expected then false
    else (
      r := desired;
      true))
