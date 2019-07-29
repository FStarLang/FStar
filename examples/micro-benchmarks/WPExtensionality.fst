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

open FStar.Tactics

assume val wp1 : (int -> Type0) -> Type0
assume val wp2 : (int -> unit -> Type0) -> Type0

(* 1 arg direct *)
let direct_1 ()
= assert True
      by (let tm = quote (forall p. (forall x. p x) ==> wp1 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp1 (fun (_:int) -> True)))
          then ()
          else fail "failed")

(* 2 arg direct *)
let direct_2 ()
= assert True
      by (let tm = quote (forall p. (forall x y. p x y) ==> wp2 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> True)))
          then ()
          else fail "failed")

(* 1 arg indirect *)
let indirect_1
= assert True
      by (admit();
          let tm = quote (forall p. (forall x. p x <==> True) ==> wp1 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp1 (fun (_:int) -> True)))
          then ()
          else fail "failed")

(* 2 arg indirect *)
let indirect_2 ()
= assert True
      by (admit ();
          let tm = quote (forall p. (forall x y. p x y <==> True) ==> wp2 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> True)))
          then ()
          else fail "failed")

(* 1 arg negated direct *)
let neg_direct_1 ()
= assert True
      by (let tm = quote (forall p. (forall x. ~(p x)) ==> wp1 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp1 (fun (_:int) -> False)))
          then ()
          else fail "failed")

(* 2 arg negated direct *)
let neg_direct_2 ()
= assert True
      by (let tm = quote (forall p. (forall x y. ~(p x y)) ==> wp2 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> False)))
          then ()
          else fail "failed")

(* 1 arg negated indirect *)
let neg_indirect_1 ()
= assert True
      by (admit();
          let tm = quote (forall p. (forall x. p x <==> False) ==> wp1 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp1 (fun (_:int) -> False)))
          then ()
          else fail "failed")

(* 2 arg negated indirect *)
let neg_indirect_2 ()
= assert True
      by (admit ();
          let tm = quote (forall p. (forall x y. p x y <==> False) ==> wp2 p) in
          debug ("before = " ^ term_to_string tm);
          let tm' = norm_term [simplify] tm in
          debug ("after= " ^ term_to_string tm');
          if term_eq tm' (`(wp2 (fun (_:int) (_:unit) -> False)))
          then ()
          else fail "failed")

// Bug reported by Jay
[@expect_failure]
let bug () : Lemma False =
   ((if true then () else ()); ())
