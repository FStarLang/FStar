module Steel.Effects2.Tests

open Steel.Memory
open Steel.Effects2

assume val ref : Type0
assume val ptr (_:ref) : hprop u#1

assume val alloc (x:int)  : SteelT ref emp ptr
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)

[@@expect_failure]
let test1 (x:int) : SteelT ref emp ptr = alloc x

// #set-options "--debug Steel.Effects2.Tests --debug_level LayeredEffectsEqns --ugly"
[@@expect_failure]
let test2 (r1 r2:ref) : SteelT (int & int) (ptr r1 `star` ptr r2) (fun _ -> ptr r1 `star` ptr r2) =
  let x = read r1 in
  let y = read r2 in
  steel_ret (x, y)
