module Tests

open Eq
open Add
open Num

let rec sum (#a:Type) [|additive a|] (l : list a) : a =
    match l with
    | [] -> zero
    | x::xs -> plus x (sum xs)

let sum2 (#a:Type) [|additive a|] (l : list a) : a =
    List.Tot.fold_right plus l zero

let _ = assert_norm (sum2 [1;2;3;4] == 10)
let _ = assert_norm (sum2 [false; true] == true)

let sandwich (#a:Type) [|num a|] (x y z : a) : a =
    if eq x y
    then plus x z
    else minus y z

let test1 = assert (sum [1;2;3;4;5;6] == 21)
let test2 = assert (plus 40 (minus 10 8) == 42)
