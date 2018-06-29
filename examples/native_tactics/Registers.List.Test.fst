module Registers.List.Test
open Registers.List

let regs = regmap int

(*  None of these tests can be run in a reasonable amount of time
//     with the interpreter. But they run pretty quickly with native
//     compilation *)
let concrete_integer_map  =
    let r = identity_map 10000 (create 0) in
    assert_norm (sel r 10000 == 10000)

let symbolic_map_contents_1 (x:int) (y:int) =
    let r = const_map_n 10000 x (create y) in
    assert (normalize_term (sel r 10000) == x)

let symbolic_map_contents_2 (x:int) (y:int) =
    let r = const_map_n 10000 x (create y) in
    assert (normalize_term (sel r 20000) == y)

/// Not sure why, but this one fails to actually normalize
/// Turn on this debugging flag to see the unnormalized term fed to Z3
/// Needs to be debugged
let symbolic_map_contents_3 (x:int) (y:int) =
    let r = const_map_n 1000 x (create y) in
    assert_norm (sel r 1000 == x);
    assert_norm (sel r 1001 == y)
