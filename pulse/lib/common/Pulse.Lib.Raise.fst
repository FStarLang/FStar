(*
   Copyright 2025 Microsoft Research

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
module Pulse.Lib.Raise
module U = FStar.Universe

type punit : Type u#a = | PUnit

let raisable : p:prop { Type u#(max a b) } =
  squash (
    Squash.return_squash (punit u#(max a b));
    subtype_of (Type u#(max a b)) (Type u#b)
  )

let raisable_non_info : non_informative (raisable u#a u#b) =
  { reveal = ((fun p -> p) <: Ghost.erased (raisable u#a u#b) -> raisable u#a u#b) }

let raisable_inst = ()

let elim_subtype (#a: Type u#a) (#b: Type u#b { subtype_of a b }) (x: a) : b = x

let raise_t t = elim_subtype (U.raise_t u#a u#b t)

let raise_val x = U.raise_val u#a u#b x
let downgrade_val x = U.downgrade_val u#a u#b x

let downgrade_val_raise_val x = U.downgrade_val_raise_val u#a u#b x
let raise_val_downgrade_val x = U.raise_val_downgrade_val u#a u#b x
