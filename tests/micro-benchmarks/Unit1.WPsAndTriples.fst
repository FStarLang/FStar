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
module Unit1.WPsAndTriples

(* Weakest-precondition transformers are gone: a computation type is just
   [M t (requires pre) (ensures post)].  What is left to test here is that
   one can abstract over a Hoare triple. *)

val f : x:int -> PURE int (requires x > 0) (ensures fun y -> y == x + 1)
let f x = assert (x > 0); x + 1

val h : #req:(int -> prop) -> #ens:(int -> int -> prop) -> $f:(x:int -> Pure int (req x) (ens x)) -> y:int -> Pure int (req y) (ens y)
let h #req #ens f x = f x

val g : x:int -> Pure int (b2t (x > 0)) (fun y -> y == x + 1)
let g = h #(fun x -> b2t (x > 0)) #(fun x y -> y == x + 1) f

val good_hoare : unit -> Pure int True (fun r -> r == 3)
let good_hoare () = 3

[@@ expect_failure [19]]
let bad_hoare () : Pure int True (fun r -> r == 3) = 4
