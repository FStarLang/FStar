module TestBoundedIntegers
open BoundedIntegers
let x : int32 = 1l
let y : int32 = 2l

let g (x:int32) : int32 = if x < BoundedIntegers.int32_max_value then x + 1l else x
let f (x:int32{0 <= x}) (y:int32{0 <= y /\ y <= x}) : int32 = x - ((x - y) / 2l)
let h (x:int32{0 <= x}) (y:int32{0 <= y /\ y <= x}) : int32 = (x + y) / 2l
