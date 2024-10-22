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
module Bug052

val trivial_a: x:nat -> y:nat -> Lemma (x + y = y + x)
let trivial_a x y = ()

val trivial_b: x:nat -> y:nat -> Lemma (x + y = y + x)
let trivial_b x y = trivial_a x y

val trivial_c: x:nat -> y:nat -> Lemma (x + y = y + x)
let trivial_c x y = trivial_a x y

val use_fact_and_lemma: x:nat -> y:nat -> Tot nat
let use_fact_and_lemma x y =
  trivial_c x y;
  trivial_a x y;
  let _ = trivial_b x in
  x + y

val test: unit -> Tot unit
let test () = assert (use_fact_and_lemma 0 1 = 1)
