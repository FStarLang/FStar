module Steel.Closure

open Steel.Effect
open Steel.Memory
open Steel.Reference
open Steel.SteelT.Basics
open Steel.FractionalPermission

let repr (r:ref int) (x:int) = pts_to r full_perm x

let ctr (r:ref int) = prev:erased int  -> SteelT (y:int{y == prev + 1}) (repr r prev) (repr r)

let next (r:ref int) (prev:erased int)
  : SteelT (y:int{y == prev + 1}) (repr r prev) (repr r)
  = let v = read r in
    write r (v + 1);
    return (v + 1)

let new_counter () =
  let x = alloc 0 in
  let f : ctr x = next x in
  return #ctr_t #(fun r -> dfst r 0) (| repr x, f |)
