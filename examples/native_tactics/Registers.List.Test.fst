module Registers.List.Test
open Registers.List

let regs = regmap int

// (*  None of these tests can be run in a reasonable amount of time
// //     with the interpreter. But they run pretty quickly with native
// //     compilation *)
// let concrete_integer_map  =
//     let r = identity_map 10000 (create 0) in
//     assert_norm (sel r 10000 == 10000)

// let rec copy_map (n:nat) (in_r:regs) (out_r:regs) =
//     if n = 0 then out_r
//     else copy_map (n - 1) in_r (upd out_r n (sel in_r n))

assume val my_assert: i:int -> j:int -> Lemma (requires (normalize_term i == j)) (ensures True)
let concrete_integer_map  =
    let f r = upd r 1 1 in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let f r = f (f r) in
    let r = f (create 0) in
    my_assert (sel r 0) 0
//    assert_norm (sel r 1 == 1) //(copy_map 10000 r (create 0)) 10000 == 10000)

// let symbolic_map_contents_1 (x:int) (y:int) =
//     let r = const_map_n 10000 x (create y) in
//     assert (normalize_term (sel r 10000) == x)

// let symbolic_map_contents_2 (x:int) (y:int) =
//     let r = const_map_n 10000 x (create y) in
//     assert (normalize_term (sel r 20000) == y)

// /// Not sure why, but this one fails to actually normalize
// /// Turn on this debugging flag to see the unnormalized term fed to Z3
// /// Needs to be debugged
// let symbolic_map_contents_3 (x:int) (y:int) =
//     let r = const_map_n 10000 x (create y) in
//     assert_norm (sel r 10000 == x);
//     assert_norm (sel r 10001 == y)
