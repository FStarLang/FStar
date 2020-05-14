module Steel.Closure

open Steel.Effect
open Steel.Memory


val new_counter (u:unit) :
  SteelT (p:hprop & (unit -> SteelT unit p (fun _ -> p)))
        emp
        (fun r -> dfst r)
