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
module EnumEq

open Enum
open Eq
open FStar.Tactics.Typeclasses

(* Trying out a "class morphism", a post-facto relation between two existing classes. *)
instance enum_eq (#a:Type) (d : enum a) : deq a = {
    eq    = (fun (x y : a) -> toInt x = toInt y);
    eq_ok = (fun (x y : a) -> inv1 x; inv1 y);
}

let test #a [|enum a|] (x y : a) : bool =
  eq x y
