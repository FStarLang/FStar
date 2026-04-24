(*
   Copyright 2008-2024 Microsoft Research

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

(** Given a classical proof of [exists x. p x], we can exhibit an erased
    (computationally irrelevant) a witness [x:erased a] validating
    [p x].  *)
irreducible
let indefinite_description_ghost (a: Type) (p: (a -> prop) { exists x. p x })
  : GTot (x: a { p x })
  = indefinite_description p

(** A version in ghost is easily derivable *)
let indefinite_description_tot (a:Type) (p:(a -> prop) { exists x. p x })
  : Tot (w:Ghost.erased a{ p w })
  = Ghost.hide (indefinite_description_ghost a p)

(** Indefinite description entails the a strong form of the excluded
    middle, i.e., one can case-analyze the truth of a proposition
    (only in [Ghost]) *)
let strong_excluded_middle (p: prop) : GTot (b: bool{b = true <==> p}) =
  p

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