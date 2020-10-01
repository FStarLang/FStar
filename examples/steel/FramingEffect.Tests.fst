module FramingEffect.Tests

open Steel.Memory
open Steel.FramingEffect

open FStar.Tactics

[@@ resolve_implicits; framing_implicit]
let resolve_tac () : Tac unit =
  //dump "All goals:";
  admit_all ()


assume val ref : Type0
assume val ptr (_:ref) : slprop u#1

assume val alloc (x:int)  : SteelT ref emp ptr
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)

// #set-options "--debug Steel.Effects2.Tests --debug_level ResolveImplicitsHook --ugly // --print_implicits"
// #set-options "--debug Steel.Effects2.Tests --debug_level LayeredEffectsEqns --ugly // --debug_level ResolveImplicitsHook --print_implicits --debug_level Extreme // --debug_level Rel --debug_level TwoPhases"
[@@expect_failure]
let test1 (x:int) : SteelT ref emp ptr = 
  alloc x

// #set-options "--debug Steel.Effects2.Tests --debug_level Extreme --debug_level Rel --debug_level LayeredEffectsEqns --print_implicits --ugly --debug_level TwoPhases --print_bound_var_types"
[@@expect_failure]
let test2 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r) =
  let x = read r in
  x
  //steel_ret x


// [@@expect_failure]
// let test2 (r1 r2:ref) : SteelT (int & int) (ptr r1 `star` ptr r2) (fun _ -> ptr r1 `star` ptr r2) =
//   let x = read r1 in
//   let y = read r2 in
//   steel_ret (x, y)
