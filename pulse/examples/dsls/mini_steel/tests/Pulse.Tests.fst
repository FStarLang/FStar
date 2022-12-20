module Pulse.Tests
module T = FStar.Tactics
open Pulse.Steel.Wrapper
open Pulse.Syntax
open Pulse.Main

%splice_t[foo] (main (Tm_Constant (Bool true)) Tm_Emp)
%splice_t[bar] (check_bar ())

// "(fun (n:erased) (r:ref) (x:u32) -> \
//             { pts_to r (reveal n) } call: write(r, x))"
//       "emp")
            
// (
// Tm_Abs
//   (Tm_FVar erased_lid)  //n:erased u32
//   Tm_Emp
//   (Tm_Abs
//      (Tm_FVar ref_lid)  //r:ref
//      Tm_Emp
//      (Tm_Abs
//         (Tm_FVar u32_lid)  //x:u32
//         (Tm_PureApp
//           (Tm_PureApp
//              (Tm_FVar pts_to_lid)
//              (Tm_BVar 1))
//           (Tm_PureApp
//              (Tm_FVar reveal_lid)
//              (Tm_BVar 2))
//         )
//         (Tm_STApp
//            (Tm_PureApp
//               (Tm_PureApp
//                  (Tm_FVar write_lid)
//                  (Tm_BVar 2)
//               )
//               (Tm_BVar 1)
//            )
//            (Tm_BVar 0)
//         )
//      )
//   )
// )
// Tm_Emp
// )
