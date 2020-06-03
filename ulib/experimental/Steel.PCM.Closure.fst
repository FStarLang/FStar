module Steel.PCM.Closure

open Steel.PCM.Effect
open Steel.PCM.Memory
open Steel.PCM.Reference
open Steel.PCM.SteelT.Basics
open Steel.PCM.FractionalPermission

let repr (r:ref int) (x:int) = pts_to r full_perm x

let ctr (r:ref int) = prev:erased int  -> SteelT (y:int{y == prev + 1}) (repr r prev) (repr r)

val next (r:ref int) : ctr r
let next (r:ref int) (prev:erased int)
  = let v = read r in
    write r (v + 1);
    return (v + 1)

let new_counter () =
  let x = alloc 0 in
  h_assert (repr x 0);
  let f : ctr x = next x in
  let r : ctr_t = (| repr x, f |) in
  return #ctr_t #(fun r -> dfst r 0) r
