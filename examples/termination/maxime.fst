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
module Maxime

(* Maxime is worried that this fixpoint will be accepted if we were to add
   f x << f *)

(* This example is due to Thierry Coquand and Christine Paulin.
   Should be in here: https://hal.inria.fr/tel-00431817/document
 *)

noeq
type foo = | C : (p:Type -> p -> Tot p) -> foo


(* Let it to the SMT solver:
assume Axiom1 : (forall (a:Type) (b:Type) (f:(a -> Tot b)) (x:a). f x << f)

-- this one fails anyway with unsolved unification variable,
   even with type annotation
assume val axiom2 : (forall (b:Type) (f:(a:Type -> Tot b)) (c:Type).
                     Precedes #b #(a:Type -> Tot b) (f c) f)
 *)
(* Manual instantiation: *)
assume val axiom1 : a:Type -> b:Type -> f:(a -> Tot b) -> x:a ->
                    Lemma (f x << f)

assume val axiom2 : b:(Type->Type) -> f:(a:Type -> Tot (b a)) -> c:Type ->
                    Lemma (f c << f)



#set-options "--print_universes"
(* val bad : x:foo -> Tot False (decreases x) *)
let rec bad (x:foo) : Tot False (decreases x) =
  match x with
  | C f -> (axiom2 (fun (p:Type) -> (p -> Tot p)) f foo;
            (* assert(f foo << f); -- this should hold now, F* bug? *)
            assert (f foo << f) ;
            (* admitP (f foo << f); *)
            axiom1 foo foo (f foo) x;
            assert(f foo x << f);
            bad (f foo x))

(* Without the axioms:
val bad : x:foo -> Tot False (decreases x)
let rec bad (x:foo) : False =
  match x with
  | C f -> bad (f foo x)

   Current error message:
   Error maxime.fst(9,0-15,0): The following problems were found:
	Subtyping check failed; expected type _12724:foo{(%[_12724] << %[x])}; got type foo (maxime.fst(11,15-11,24)) *)
