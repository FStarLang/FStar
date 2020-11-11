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

    Given a proof of [p], we can obtain a witness for [p] in [GTot].
*)
assume
val indefinite_unsquash (#p:Type) (x:squash p) : GTot p

(*
    Indefinite description:

    Given a classical proof of [exists x. p x], we can exhibit an erased
    (computationally irrelevant) a witness [x:erased a] validating
    [p x].
*)
val indefinite_description_tot (a:Type) (p:(a -> prop) { exists x. p x })
  : Tot (w:Ghost.erased a{ p w })
let indefinite_description_tot a p =
  let sq0 : squash (exists x. p x) = () in
  let sq1 : squash (x:a & p x) = Squash.join_squash sq0 in
  let (| w, pf |) = indefinite_unsquash sq1 in
  w

(** A version in ghost is easily derivable *)
let indefinite_description_ghost (a: Type) (p: (a -> prop) { exists x. p x })
  : GTot (x: a { p x })
  = let w = indefinite_description_tot a p in
    let x = Ghost.reveal w in
    x

(** An alternate formulation, mainly for legacy reasons.

    Given a classical proof of [exists x. p x], we can exhibit (ghostly) a
    witness [x:a] validating [p x].

    We should take [p] to be [a -> prop]. However, see
    [Prims.prop] for a description of the ongoing work on more
    systematically using [prop] in the libraries *)
[@@deprecated "Consider using indefinite_description_ghost instead"]
val indefinite_description (a: Type) (p: (a -> GTot Type0))
  : Ghost (x: a & p x) (requires (exists x. p x)) (ensures (fun _ -> True))
let indefinite_description a p =
  let sq0 : squash (exists x. p x) = () in
  let sq1 : squash (x:a & p x) = Squash.join_squash sq0 in
  indefinite_unsquash sq1

open FStar.Classical
open FStar.Squash

(** Indefinite description entails the a strong form of the excluded
    middle, i.e., one can case-analyze the truth of a proposition
    (only in [Ghost]) *)
let strong_excluded_middle (p: Type0) : GTot (b: bool{b = true <==> p}) =
  let tf : squash (p \/ ~p) = () in
  match indefinite_unsquash (Squash.join_squash tf) with
  | Left  _ -> true
  | Right _ -> false

(** We also can combine this with a the classical tautology converting
    with a [forall] and an [exists] to extract a witness of validity of [p] from
    a classical proof that [p] is not universally invalid.

    Note, F*+SMT can easily prove, since it is just classical logic:
      [(~(forall n. ~(p n))) ==> (exists n. p n) ] *)
let stronger_markovs_principle (p: (nat -> GTot bool))
    : Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n)) =
    indefinite_description_ghost _ (fun n -> p n==true)

(** A variant of the previous lemma, but for a [prop] rather than a
    boolean predicate *)
let stronger_markovs_principle_prop (p: (nat -> GTot prop))
    : Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n)) =
    indefinite_description_ghost _ p

(** The axiom of choice in Ghost.

    From a function [f] that, for every [x:a], (ghostly) produces a [b],
    we can (ghostly) obtain a total function from [a] to [b]. Further,
    this new function is pointwise equal to [f].
*)
val ghost_choice (#a:Type) (#b:Type) (f:(a -> GTot b))
  : Ghost (a -> b)
          (requires True)
          (ensures fun f' -> forall x. f x == f' x)
let ghost_choice #a #b f =
  let fs (x:a) : squash (y:b{y == f x}) = Squash.return_squash (f x) in
  indefinite_unsquash (push_squash fs)
