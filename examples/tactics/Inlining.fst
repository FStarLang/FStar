module Inlining

// inlining into stateful functions doesn't work in master;
// see https://github.com/FStarLang/FStar/issues/1190
// (fixed in guido_fix)

open FStar.Tactics

open FStar.HyperStack
open FStar.HyperStack.ST
module U32 = FStar.UInt32

open FStar.Buffer

// these are the primitives to be inlined

let add_1 (x:int) : int = x+1

let set_to_1 (x: buffer U32.t{length x == 1}) =
  x.(0ul) <- 1ul

// eg, we want to inline add_1 into this function
let add_2 (x:int) : int = add_1 (add_1 x)

// eg, we want to inline add_1 in this function
let create_add_1 (u:unit) : St unit =
  push_frame();
  let x = create 0ul (U32.uint_to_t (add_1 1)) in
  pop_frame();
  ()

let normalize (#t:Type) (x:t) : tactic unit =
  dup;;
  exact (quote x);;
  norm [Delta; UnfoldOnly [pack_fv ["Inlining"; "add_1"]; pack_fv ["Inlining"; "set_to_1"]]];;
  trefl

// add_2' is like add_2 but has add_1 inlined (printing verifies this)
let add_2' : int -> int = synth_by_tactic (normalize ((fun (x:int) -> add_1 (add_1 x))))

let create_add_1' : unit -> St unit = synth_by_tactic (normalize ((fun (u:unit) ->
             push_frame();
             let x = create 0ul (U32.uint_to_t (add_1 1)) in
             pop_frame();
             ()) <: unit -> St unit))

// we want to inline set_to_1 in this function
let create_and_set (u:unit) : St unit =
  push_frame();
  let x = create 0ul 1ul in
  set_to_1 x;
  pop_frame();
  ()

let create_and_set' : unit -> St unit =
  synth_by_tactic (normalize ((fun (u:unit) ->
    push_frame();
    let x = create 0ul 1ul in
    set_to_1 x;
    pop_frame();
    ()) <: unit -> St unit))
