module Steel.SpinLock
open Steel.Effect
open Steel.Memory

val lock (p:hprop u#1) : Type u#0

val new_lock (p:hprop u#1)
  : SteelT (lock p) p (fun _ -> emp)

val acquire (#p:hprop u#1) (l:lock p)
  : SteelT unit emp (fun _ -> p)

val release (#p:hprop u#1) (l:lock p)
  : SteelT unit p (fun _ -> emp)
