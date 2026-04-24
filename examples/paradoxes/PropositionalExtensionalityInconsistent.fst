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

module PropositionalExtensionalityInconsistent
(* With prop being opaque (Type0), many of the paradoxes related to
   propositional extensionality over all of Type0 are no longer expressible.
   We keep the file but mark the proofs that relied on Type0/prop confusion
   as expected failures. *)

(* PropositionalExtensionality for prop is actually fine *)
let propExt_prop = forall (p1 p2:prop). (p1 <==> p2) <==> p1==p2

(* The proof relied on int <==> unit, which no longer works since
   <==> requires prop operands *)
[@@(expect_failure [189])]
let propExt_Type_inconsistent ()
  : Lemma (requires propExt_prop)
          (ensures False)
  = let int_is_inhabited (x:int) : Lemma (int <==> unit) = () in
    int_is_inhabited 42

(* sub_singleton over prop *)
let sub_singleton = a:prop{forall (x y:squash a). x == y}
let propExt_sub_singleton = forall (p1 p2:sub_singleton). (p1 <==> p2) <==> p1==p2

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
[@@(expect_failure [19])]
let propExt_sub_singleton_inconsistent()
  : Lemma (requires propExt_sub_singleton)
          (ensures False)
  = ()
#pop-options


(* predicate extensionality over prop predicates *)
let predicate (a:Type0) = a -> Tot prop
let peq (#a:Type0) (p1 p2:predicate a) =
  forall x. p1 x <==> p2 x
let predExt_prop =
    a:Type
    -> p1:predicate a
    -> p2:predicate a
    -> Lemma (requires (peq p1 p2))
            (ensures (p1 == p2))

(* The proof relied on trivial vs unit being different types but
   equivalent propositions. With prop, this is no longer expressible. *)
[@@(expect_failure [189])]
let predExt_prop_inconsistent (ax:predExt_prop)
  : Lemma False
  = let p1 : predicate int = fun n -> trivial in
    let p2 : predicate int = fun n -> unit in
    ax int p1 p2
