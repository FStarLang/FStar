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
module StrictUnfolding
(* This is a test case for the `FStar.Pervasives.strict_on_arguments` attribute *)
open FStar.Integers
open FStar.Tactics

[@(strict_on_arguments [1])]
let project #a (x:option a{Some? x}) =
  match x with
  | Some v -> v

let test1 (x:option (x:int{x = 0}){Some? x}) =
  assert (project x == 0) //this doesn't reduce since x does not have a constant head symbol
    by (dump "A";
        norm [delta; iota];
        dump "B";
        smt ()) //so the proof has to go to SMT

let test2 () =
  assert (project (Some 0) == 0) //this one reduces to 0
    by (dump "A";
        norm [delta; iota];
        dump "B";
        trefl()) //and is dispatched by reflexivity

let test_integer_generic #sw (x:int_t sw) (y:int_t sw{ok (+) x y}) : unit =
  assert (v (x + y) == (v x + v y))

//specifically remove the overloading layer from the SMT context
#set-options "--using_facts_from '* -FStar.Integers'"

//generic integer operations do not reduce, so you cannot prove
//properties about them without also having FStar.Integers in scope
[@(expect_failure [19])]
let test_integer_generic_wo_fstar_integers sw =
  assert (forall (x y:int_t sw). ok (+) x y ==> v (x + y) == (v x + v y))
      by (norm [delta; iota]; smt())

//but, specific instances of them do reduce fully and
//and proofs about them only rely on the underlying machine integer models
let test_int_64 : unit =
  assert (forall (x y:uint_64). ok (+) x y ==> (v (x + y) == (v x + v y)))
      by (norm [delta;iota]; smt())

(* the code below extracts with `fstar --codegen OCaml` to
let (test_extraction_generic :
  FStar_Integers.signed_width -> Obj.t -> Obj.t -> Obj.t -> Obj.t -> Obj.t) =
  fun sw  ->
    fun w  ->
      fun x  ->
        fun y  ->
          fun z  ->
            FStar_Integers.op_Plus sw w
              (FStar_Integers.op_Plus sw x (FStar_Integers.op_Plus sw y z))
*)
let test_extraction_generic #sw (w x y z:int_t sw) : int_t sw =
  assume (ok (+) y z);
  assume (ok (+) x (y + z));
  assume (ok (+) w (x + (y + z)));
  w + (x + (y + z))

(* the code below extracts with `fstar --codegen OCaml` to

let (test_extraction_specific :
  FStar_UInt64.t ->
    FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun w  ->
    fun x  ->
      fun y  ->
        fun z  ->
          FStar_UInt64.add w (FStar_UInt64.add x (FStar_UInt64.add y z))
*)
let test_extraction_specific (w x y z:uint_64) : uint_64 =
  assume (ok (+) y z);
  assume (ok (+) x (y + z));
  assume (ok (+) w (x + (y + z)));
  w + (x + (y + z))
