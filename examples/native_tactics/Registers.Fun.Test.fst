module Registers.Fun.Test
open Registers.Fun

let regs = regmap int

assume val assert_eq: i:int -> j:int -> Lemma (requires (normalize_term i == j)) (ensures True)

(*  None of these tests can be run in a reasonable amount of time
    with the interpreter. But they run pretty quickly with native
    compilation *)

let concrete_integer_map_0  =
    let v =
      (//embed abs
        (sel
           (//unembed regmap abs
             (//embed regmap abs
              (create
                (//unembed int
                  0))))
          (//unembed int
            3))) in
    assert_eq v 0

// let concrete_integer_map_1  =
//     let v =
//       (//embed abs
//         (sel
//           (//unembed regmap abs
//             (//embed regmap int
//               (identity_map
//                 (//unembed int
//                   3)
//                 (//unembed regmap int
//                   (//embed regmap abs
//                     (create
//                       (//unembed int
//                         0)))))))
//           (//unembed int
//             3))) in
//     assert_eq v 3

// let concrete_integer_map_2 =
//     let mk r  =
//       let f r = (//embed (regmap abs)
//                   upd (//unembed (regmap abs)
//                       r)
//                     (//unembed int
//                       1)
//                     (//unembed (regmap abs)
//                       (//embed (regmap abs)
//                         (sel (//unembed (regmap abs)
//                               r)
//                              (//unembed int
//                               1))))) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       let f r = f (f r) in
//       f r
//     in
//     let r = mk (create 0) in
//     assert_eq (sel r 0) 0

// let symbolic_map_contents_1 (x:int) (y:int) =
//     let r = const_map_n 10000 x (create y) in
//     assert_eq (sel r 10000) x

// let symbolic_map_contents_2 (x:int) (y:int) =
//     let r = const_map_n 10000 x (create y) in
//     assert_eq (sel r 20000) y

// let symbolic_map_contents_3 (x:int) (y:int) =
//     let r = const_map_n 10000 x (create y) in
//     assert_eq (sel r 10000) x;
//     assert_eq (sel r 10001) y
