module Steel.Closure

open Steel.Effect
open Steel.Memory
open FStar.Ghost

let ctr_t = (p:(int -> slprop) & (x:erased int -> SteelT (y:int{y == x + 1}) (p x) p))

val new_counter (u:unit) :
  SteelT ctr_t emp (fun r -> dfst r 0)
