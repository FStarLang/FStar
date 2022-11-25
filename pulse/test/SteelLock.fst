module SteelLock

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.SpinLock

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let r = malloc 0ul in
  let l = new_lock (vptr r) in
  acquire l;
  write r 1ul;
  release l;
  0l
