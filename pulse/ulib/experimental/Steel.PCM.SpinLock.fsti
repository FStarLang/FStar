module Steel.PCM.SpinLock
open Steel.PCM.Effect
open Steel.PCM.Memory

val lock_t : Type u#0
val protects (l:lock_t) (p:slprop u#1) : prop

let lock (p:slprop u#1) = l:lock_t{l `protects` p}

val new_lock (p:slprop)
  : SteelT (lock p) p (fun _ -> emp)

val acquire (#p:slprop) (l:lock p)
  : SteelT unit emp (fun _ -> p)

val release (#p:slprop) (l:lock p)
  : SteelT unit p (fun _ -> emp)
