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

/// Indefinite description is an axiom that allows picking a witness
/// for existentially quantified predicate.
///
/// Many other axioms can be derived from this one: Use it with care!
///
/// For some background on the axiom, see:
///
/// https://github.com/coq/coq/wiki/CoqAndAxioms#indefinite-description--hilberts-epsilon-operator
/// https://en.wikipedia.org/wiki/Theory_of_descriptions#Indefinite_descriptions

(** The main axiom:

    Given a classical proof of [exists x. p x], we can exhibit (ghostly) a
    witness [x:a] validating [p x].

    TODO: we should take [p] to be [a -> prop]. However, see
    [Prims.prop] for a description of the ongoing work on more
    systematically using [prop] in the libraries *)
assume
val indefinite_description (a: Type) (p: (a -> GTot Type0))
    : Ghost (x: a & p x) (requires (exists x. p x)) (ensures (fun _ -> True))

open FStar.Classical
open FStar.Squash

(** Indefinite description entails the a strong form of the excluded
    middle, i.e., one can case-analyze the truth of a proposition
    (only in [Ghost]) *)
let strong_excluded_middle (p: Type0) : GTot (b: bool{b = true <==> p}) =
  let aux (p: Type0) : Lemma (exists b. b = true <==> p) =
    give_proof (bind_squash (get_proof (l_or p (~p)))
          (fun (b: l_or p (~p)) ->
              bind_squash b
                (fun (b': c_or p (~p)) ->
                    match b' with
                    | Left hp ->
                      give_witness hp;
                      exists_intro (fun b -> b = true <==> p) true;
                      get_proof (exists b. b = true <==> p)
                    | Right hnp ->
                      give_witness hnp;
                      exists_intro (fun b -> b = true <==> p) false;
                      get_proof (exists b. b = true <==> p))))
  in
  aux p;
  match indefinite_description bool (fun b -> b = true <==> p) with
  | Mkdtuple2 b p ->
    give_witness p;
    b

(** We also can combine this with a the classical tautology converting
    with a [forall] and an [exists] to extract a witness of validity of [p] from
    a classical proof that [p] is not universally invalid.

    Note, F*+SMT can easily prove, since it is just classical logic:
      [(~(forall n. ~(p n))) ==> (exists n. p n) ] *)
let stronger_markovs_principle (p: (nat -> GTot bool))
    : Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n)) =
  match indefinite_description _ (fun n -> b2t (p n)) with
  | Mkdtuple2 n p ->
    give_witness p;
    n

(** A variant of the previous lemma, but for a [prop] rather than a
    boolean predicate *)
let stronger_markovs_principle_prop (p: (nat -> GTot prop))
    : Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n)) =
  match indefinite_description _ p with
  | Mkdtuple2 n p ->
    give_witness p;
    n

