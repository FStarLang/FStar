module Steel.PCM.SpinLock
open Steel.PCM.Effect
open Steel.PCM.Memory

val lock (p:slprop u#1) : Type u#0

val new_lock (p:slprop)
  : SteelT (lock p) p (fun _ -> emp)

val acquire (#p:slprop) (l:lock p)
  : SteelT unit emp (fun _ -> p)

val release (#p:slprop) (l:lock p)
  : SteelT unit p (fun _ -> emp)
