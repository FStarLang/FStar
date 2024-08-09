(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Guido Martinez, Aseem Rastogi, Nikhil Swamy
*)

module FStar.Calc

open FStar.Preorder

/// This module provides calculational proofs support
///
/// Client programs need not use it directly,
///   instead F* provides convenient syntax for writing calculational proofs
///
/// See examples/calc for some examples

/// The main type for the calc proof chain

val calc_chain (#a:Type u#a) (rs:list (relation a)) (x y:a) : Type u#(max 1 a)

/// Definition of when a calc chain is sound

[@@"opaque_to_smt"]
let rec calc_chain_related (#a:Type) (rs:list (relation a)) (x y:a)
  : Tot Type0
  = match rs with
    | [] -> x == y
      (* GM: The `:t` annotation below matters a lot for compactness of the formula! *)
    | r1::rs -> exists (w:a). calc_chain_related rs x w /\ r1 w y

[@@"opaque_to_smt"]
let calc_chain_compatible (#t:Type) (rs:list (relation t)) (p:relation t)
  : Tot Type0
  = forall (x y:t). calc_chain_related rs x y ==> p x y

/// A proof irrelevant type for the calc chains

type calc_pack (#a:Type) (rs:list (relation a)) (x y:a) =
  squash (calc_chain rs x y)

/// Initializing a calc chain

val calc_init (#a:Type) (x:a) : Tot (calc_pack [] x x)

/// A single step of the calc chain
///
/// Note the list of relations is reversed
///   calc_chain_compatible accounts for it

val calc_step
  (#a:Type)
  (#x #y:a)
  (p:relation a)                             (* Relation for this step *)
  (z:a)                                      (* Next expression *)
  (#rs:list (relation a))
  (pf:unit -> Tot (calc_pack rs x y))         (* Rest of the proof *)
  (j:unit -> Tot (squash (p y z)))            (* Justification *)
  : Tot (calc_pack (p::rs) x z)

/// Finishing a calc proof,
///   providing the top-level relation as the postcondition

val calc_finish
  (#a:Type)
  (p:relation a)
  (#x #y:a)
  (#rs:list (relation a))
  (pf:unit -> Tot (calc_pack rs x y))
  : Lemma
      (requires (norm [delta_only [`%calc_chain_compatible; `%calc_chain_related];
                       iota;
                       zeta]
                      (Range.labeled (range_of pf)
                         "Could not prove that this calc-chain is compatible"
                         (calc_chain_compatible rs p))))
      (ensures (p x y))

val calc_push_impl (#p #q:Type) (f:squash p -> GTot (squash q))
  : Tot (squash (p ==> q))
