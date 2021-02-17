module Steel.Closure

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.FractionalPermission

let repr (r:ref int) (x:int) = pts_to r full_perm x

let ctr (r:ref int) = prev:erased int  -> SteelT (y:int{y == prev + 1}) (repr r prev) (repr r)

let next (r:ref int) (prev:erased int)
  : SteelT (y:int{y == prev + 1}) (repr r prev) (repr r)
  = let v = read r in
    let (x:int { x == prev + 1 }) = v + 1 in
    write r x;
    x

val new_counter' (u:unit) :
  SteelT ctr_t emp (fun r -> dfst r 0)

let new_counter' () =
  let x = alloc 0 in
  let f : ctr x = next x in
  let res : ctr_t = (| repr x, f |) in
  change_slprop (repr x 0) (dfst res 0) (fun _ -> ());
  res

let new_counter = new_counter'
