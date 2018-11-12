(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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

let normalize (#t:Type) (x:t) : Tac unit =
  dup ();
  debug (term_to_string (quote x));
  exact (quote x);
  norm [delta; delta_only [`%(add_1)]; delta_only [`%(set_to_1)]];
  trefl ()

// add_2' is like add_2 but has add_1 inlined (printing verifies this)
let add_2' : int -> int = synth_by_tactic (fun () -> normalize ((fun (x:int) -> add_1 (add_1 x))))

let create_add_1' : unit -> St unit = synth_by_tactic (fun () -> normalize ((fun (u:unit) ->
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
  synth_by_tactic (fun () -> normalize ((fun (u:unit) ->
    push_frame();
    let x = create 0ul 1ul in
    set_to_1 x;
    pop_frame();
    ()) <: unit -> St unit))
