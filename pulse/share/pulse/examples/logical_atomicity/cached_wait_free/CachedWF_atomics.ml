(**
   Trusted sequentially consistent realization for the verified single-cell
   models. This is mutex-backed, NOT a native wait-free implementation.
   Hooks run outside the mutex and may only schedule other legal operations.
*)

let lock = Mutex.create ()
let hook = ref (fun (_ : string) -> ())

let synchronized f =
  Mutex.lock lock;
  Fun.protect ~finally:(fun () -> Mutex.unlock lock) f

let primitive kind f =
  let result, after = synchronized (fun () -> f (), !hook) in
  after kind;
  result

let read r = primitive "read" (fun () -> !r)
let write r value = primitive "write" (fun () -> r := value)
let exchange r expected desired =
  primitive "exchange" (fun () ->
    let old = !r in
    if old = expected then r := desired;
    old)

let set_hook f = synchronized (fun () -> hook := f)
