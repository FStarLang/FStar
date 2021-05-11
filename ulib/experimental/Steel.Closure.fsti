module Steel.Closure

open Steel.Memory
open Steel.Effect
open FStar.Ghost

let ctr_t = (p:(int -> vprop) & (x:erased int -> SteelT (y:int{y == x + 1}) (p x) p))

val new_counter (u:unit) :
  SteelT ctr_t emp (fun r -> dfst r 0)
