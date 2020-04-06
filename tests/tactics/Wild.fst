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
module Wild

open FStar.Tactics
open FStar.Classical

let id x = x

(* Sanity checks that we're properly tracking implicits *)
[@(expect_failure [217])] let _ = assert False by (exact (quote (id _)))
[@(expect_failure [217])] let _ = assert True  by (exact (quote (id _)))
[@(expect_failure [217])] let _ = assert False by (exact (quote _))
[@(expect_failure [217])] let _ = assert True  by (exact (quote _))

(* A more elaborate test *)

val exists_weaken: #a:Type -> p:(a -> Type) -> q:(a -> Type) -> h:(forall (x:a{p x}). q x) -> x:a{p x}
  -> GTot (squash (exists x. q x))
let exists_weaken #a p q h x = exists_intro q x

val a : Type0
let a = unit

val p : a -> Type0
let p x = True

val q : a -> Type0
let q x = False

val fact: (h:squash (exists x. p x)) -> Lemma (exists x. q x)

[@(expect_failure [217])]
let fact h =
   assert (exists x. q x)
       by (apply_lemma (`exists_elim);
           exact (quote h);
           exact (quote (fun x -> exists_weaken p q _ x)))
