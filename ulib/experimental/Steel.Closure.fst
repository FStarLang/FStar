module Steel.Closure

open Steel.Effect
open Steel.Memory
open Steel.Reference
open Steel.FractionalPermission
module SX = Steel.EffectX
open Steel.SteelXT.Basics

let repr (r:ref int) (x:int) = pts_to r full_perm x

let ctr (r:ref int) = prev:erased int  -> SX.SteelXT (y:int{y == prev + 1}) (repr r prev) (repr r)

let next (r:ref int) (prev:erased int)
  : SX.SteelXT (y:int{y == prev + 1}) (repr r prev) (repr r)
  = let v = as_steelx (fun _ -> read r) in
    as_steelx (fun _ -> write r (v + 1));
    return (v + 1)

val new_counter' (u:unit) :
  SX.SteelXT ctr_t emp (fun r -> dfst r 0)


let new_counter' () =
  let x = as_steelx (fun _ -> alloc 0) in
  let f : ctr x = next x in
  return #ctr_t #(fun r -> dfst r 0) (| repr x, f |)

let new_counter = new_counter'
