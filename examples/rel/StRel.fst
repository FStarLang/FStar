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
module StRel
open Rel
open FStar.Heap
open FStar.ST

(* Pure relational reasoning about stateful functions *)

  (* Pure functions using heap passing *)
val f1_hp : heap -> ref int -> GTot (heap * int)
let f1_hp h x = h, sel h x

val f2_hp : heap -> ref int -> Tot (heap * int)
let f2_hp h x = h, 0

  (* Stateful functions ipmlementing these pure functions *)
val f1 : x:(ref int) -> ST int (requires (fun h -> True))
                               (ensures  (fun h r h' -> fst (f1_hp h x) == h'
                                                     /\ snd (f1_hp h x) == r))
let f1 x = !x

val f2 : x:(ref int) -> ST int (requires (fun h -> True))
                               (ensures  (fun h r h' -> fst (f2_hp h x) == h'
                                                     /\ snd (f2_hp h x) == r))
let f2 x = 0

val glift : #t:Type -> #t2:Type
           -> f:(t -> GTot t2) -> rel t
           -> GTot (rel t2)
let glift #t #t2 f (R x y) = R (f x) (f y)

val glift2 : #t:Type -> #t2:Type -> #t3:Type
           -> f:(t -> t2 -> GTot t3) -> rel t -> rel t2
           -> GTot (rel t3)
let glift2 #t #t2 #t3 f (R x y) (R x2 y2) = R (f x x2) (f y y2)

  (* Proving relational properties using pure lemmas *)
val f1_ni : h:(eq heap) -> x:(eq (ref int)) 
    -> Lemma (r_eq (lift snd (glift2 f1_hp h x)))
let f1_ni h x = ()

val f2_ni : h:(rel heap) -> x:(rel (ref int)) 
    -> Lemma (r_eq (lift snd (lift2 f2_hp h x)))
let f2_ni h x = ()
