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
module Bug756



val e1 : f:(int -> Tot int) -> Lemma ((fun x -> f x) == f)
let e1 f = ()

val e2 : f:(int -> int -> Tot int) -> Lemma ((fun x -> f x) == f)
let e2 f = ()

val e3 : f:(int -> int -> Tot int) -> x:int -> Lemma ((fun y -> (f x) y) == (f x))
let e3 f x = admit () // e1 (f x)

open FStar.FunctionalExtensionality

val e3' : f:(int -> int -> Tot int) -> x:int -> Lemma ((fun y -> (f x) y) `feq` f x)
let e3' f x = () // e1 (f x)
