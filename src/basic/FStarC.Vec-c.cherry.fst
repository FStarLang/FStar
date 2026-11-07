(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Vec

(* The Cherry implementation: a reference to an immutable array, which
   [push] takes out of the reference so that it is uniquely owned and
   Cherry's [IA.push] grows it in place.  [length] and [get] borrow the
   vector, and read it without counting the array (Cherry's ref peek). *)

open FStarC.Effect
module S = FStarC.SmallInt
module IA = FStar.ImmutableArray

type vec (a:Type) = ref (IA.t a)

let singleton #a x = mk_ref (IA.push (IA.of_list []) x)

let length #a ([@@@FStar.Attributes.cherry_borrowed] v) = S.of_int (IA.length !v)

let get #a ([@@@FStar.Attributes.cherry_borrowed] v) i =
  let cur = !v in
  if S.(i >= zero && i < of_int (IA.length cur)) then begin
    let j = S.to_int i in
    assume (0 <= j /\ j < IA.length cur);
    IA.index cur j
  end else failwith "FStarC.Vec: index out of bounds"

let push #a ([@@@FStar.Attributes.cherry_borrowed] v) x =
  let cur = !v in
  v := IA.of_list [];
  v := IA.push cur x
