module Pulse.Checker.Common

open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Framing

// let force_st #f #g #t #pre pre_typing x =
//   let (| c, d_c |) = x in
//   match c with
//   | C_Tot ty ->
//     let (| ures, ures_ty |) = check_universe f g ty in
//     let c = return_comp_noeq ures ty in
//     let d = T_ReturnNoEq _ _ _ _ d_c ures_ty in
//     frame_empty pre_typing ures_ty _ c d        

//   | C_ST _
//   | C_STAtomic _ _
//   | C_STGhost _ _ -> (|c, d_c|)
