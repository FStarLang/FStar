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
/// for existentially quantified predicate. See the interface for more
/// context.
///
open FStar.Classical
open FStar.Squash

(** The main axiom:

    Given a classical proof of [exists x. p x], we can exhibit an erased
    (computationally irrelevant) a witness [x:erased a] validating
    [p x].
*)
irreducible
let indefinite_description_tot (a:Type) (p:(a -> prop) { exists x. p x })
  : Tot (w:Ghost.erased a{ p w })
  = admit() //this is an axiom

(** A version in ghost is easily derivable *)
let indefinite_description_ghost (a: Type) (p: (a -> prop) { exists x. p x })
  : GTot (x: a { p x })
  = let w = indefinite_description_tot a p in
    let x = Ghost.reveal w in
    x

(** Indefinite description entails the a strong form of the excluded
    middle, i.e., one can case-analyze the truth of a proposition
    (only in [Ghost]) *)
let strong_excluded_middle (p: Type0) : GTot (b: bool{b = true <==> p}) =
  let aux (p: Type0) : Lemma (exists b. b = true <==> p) =
    give_proof (bind_squash (get_proof (l_or p (~p)))
          (fun (b: l_or p (~p)) ->
              bind_squash b
                (fun (b': Prims.sum p (~p)) ->
                    match b' with
                    | Prims.Left hp ->
                      give_witness hp;
                      exists_intro (fun b -> b = true <==> p) true;
                      get_proof (exists b. b = true <==> p)
                    | Prims.Right hnp ->
                      give_witness hnp;
                      exists_intro (fun b -> b = true <==> p) false;
                      get_proof (exists b. b = true <==> p))))
  in
  aux p;
  indefinite_description_ghost bool (fun b -> b = true <==> p)

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


(** A proof for squash p can be eliminated to get p in the Ghost effect *)

let elim_squash (#p:Type u#a) (s:squash p) : GTot p =
  let uu : squash (x:p & squash trivial) =
    bind_squash s (fun x -> return_squash (| x, return_squash T |)) in
  give_proof (return_squash uu);
  indefinite_description_ghost p (fun _ -> squash trivial)
