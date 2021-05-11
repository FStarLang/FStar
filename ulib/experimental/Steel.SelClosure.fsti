module Steel.SelClosure

open Steel.Memory
open Steel.SelEffect
open FStar.Ghost

let ctr_t = (p:(int -> vprop) & (x:erased int -> SteelSelT (y:int{y == x + 1}) (p x) p))

val new_counter (u:unit) :
  SteelSelT ctr_t emp (fun r -> dfst r 0)
