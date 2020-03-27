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
module Bug209

(* Need a way to name the implicit t in the body *)

val foo : #t:Type{hasEq t} -> x:t -> Lemma (x = x)
let foo #t x = ()
(* currently getting
bug209.fst(4,0-59,0) : Error
Expected a term of type "(t:Type -> x:t -> Lemma (unit))";
got a function "(fun t x -> ())" (Curried function, but not total)
 *)

(* There are more ways to write this:
   Currently type arguments are made implicit by default,
   whether they are ticket or not *)

val foo2 : t:Type{hasEq t} -> x:t -> Lemma (x = x)
let foo2 t x = ()
(*
bug209.fst(17,0-19,3) : Error
Expected a term of type "(t:Type -> x:t -> Lemma (unit))";
got a function "(fun t x -> ())" (Curried function, but not total)
 *)
