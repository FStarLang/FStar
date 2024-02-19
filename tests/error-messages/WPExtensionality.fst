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
module WPExtensionality

open FStar.Tactics.V2

let term_eq = FStar.Reflection.V2.TermEq.term_eq

assume val wp1 : (int -> Type0) -> Type0
assume val wp2 : (int -> unit -> Type0) -> Type0

let check_eq (s:string) (t1 t2 : term) : Tac unit =
  if term_eq t1 t2 then () else
    fail (Printf.sprintf "Test %s failed\nt1 = %s\nt2 = %s" s (term_to_string t1) (term_to_string t2))

(* 1 arg direct *)
let direct_1 ()
= assert True
      by (let tm = `(forall p. (forall x. p x) ==> p 1) in
          let tm' = norm_term [simplify] tm in
          check_eq "direct_1" tm' (`True))

(* 2 arg direct *)
let direct_2 ()
= assert True
      by (let tm = `(forall p. (forall x y. p x y) ==> p 12 ()) in
          let tm' = norm_term [simplify] tm in
          check_eq "direct_2" tm' (`True))

(* 1 arg indirect *)
let indirect_1
= assert True
      by (let tm = `(forall p. (forall x. p x <==> True) ==> p 1) in
          let tm' = norm_term [simplify] tm in
          check_eq "indirect_1" tm' (`True))

(* 2 arg indirect *)
let indirect_2 ()
= assert True
      by (admit ();
          let tm = `(forall p. (forall x y. p x y <==> True) ==> p 12 ()) in
          let tm' = norm_term [simplify] tm in
          check_eq "indirect_2" tm' (`True))

// Bug reported by Jay Bosamiya
[@@expect_failure [19]]
let bug () : Lemma False =
   ((if true then () else ()); ())
