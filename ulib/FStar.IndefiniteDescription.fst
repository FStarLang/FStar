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
module FStar.IndefiniteDescription

// This is the mother of a lot of axioms, use with care!

// TODO:Type0 should be prop
assume val indefinite_description : a:Type -> p:(a->GTot Type0) -> Ghost
  (x:a & p x)
  (requires (exists x. p x))
  (ensures (fun _ -> True))

open FStar.Classical
open FStar.Squash

private let aux (p:Type0) : Lemma (exists b. b = true <==> p) =
      give_proof
        (bind_squash (get_proof (l_or p (~p)))
        (fun (b : l_or p (~p)) ->
          bind_squash b (fun (b' : c_or p (~p)) ->
            match b' with
            | Left hp -> give_witness hp;
                         exists_intro (fun b -> b = true <==> p) true;
                         get_proof (exists b. b = true <==> p)
            | Right hnp -> give_witness hnp;
                         exists_intro (fun b -> b = true <==> p) false;
                         get_proof (exists b. b = true <==> p)
          )))

val strong_excluded_middle : p:Type0 -> GTot (b:bool{b = true <==> p})
let strong_excluded_middle p =
  aux p;
  match indefinite_description bool (fun b -> b = true <==> p) with
  | Mkdtuple2 b p -> give_witness p; b

(* F* can prove this automatically, it's just classical logic *)
(* let xxx (p:nat->Type0) : Lemma (requires (~(forall n. ~(p n)))) *)
(*                                (ensures (exists n. p n)) = () *)

val stronger_markovs_principle : p:(nat -> GTot bool) -> Ghost nat
  (requires (~(forall (n:nat). ~(p n))))
  (ensures (fun n -> p n))
let stronger_markovs_principle p =
  match indefinite_description _ (fun n -> b2t (p n)) with
  | Mkdtuple2 n p -> give_witness p; n
