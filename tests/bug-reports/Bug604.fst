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
module Bug604

(* Inductive equality on integers *)
noeq type ieq : int -> int -> Type =
| Refl : x:int -> ieq x x

(* Some predicate on integers *)
assume type pred : int -> Type

val steps_preserves_red : e:int -> e':int -> b:ieq e e' -> pred e -> Tot (pred e')
let steps_preserves_red e e' heq hp =
  match heq with
  | Refl e'' -> assert(e == e'' /\ e == e'); (* -- these work fine *)
                hp                           (* -- but this doesn't *)

(* [hritcu@detained bug-reports]$ fstar.exe bug604.fst *)
(* ./bug604.fst(13,17-13,19) : Error *)
(* Expected expression of type "(Bug604.pred e')"; *)
(* got expression "hp" of type "(Bug604.pred e)" *)
