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
module Calc

open FStar.Tactics

(* This file contains advanced Kung Fu. Edit at your own peril *)

//The normalize_term's here are important, see (XXX)
let ( &= ) (#a:Type) (x:a) (y:a) :
    (unit -> Pure a (requires (normalize_term x == y))
                    (ensures (fun z -> z == y /\ normalize_term x == y)))
  = fun () -> y

(** Combinator used to discharge equalities with SMT/lemmas*)
let ( &| ) #a #req (#ens : (_:a{req}) -> GTot Type0) ($f:(unit -> Pure a req ens))
            (proof:unit -> Lemma req)
    : Tot (x:a{req /\ ens x})
  = proof (); f ()

private let rw_and_try (proof : unit -> Tac unit) () : Tac unit =
    rewrite_eqs_from_context ();
    norm[delta];
    proof ()

#reset-options "--no_tactics"
(** Combinator used to discharge equalities with tactics*)
let ( &|| ) #a (#req : Type0) (#ens : (_:a{req}) -> GTot Type0) ($f:(unit -> Pure a req ens))
      (proof: (unit -> Tac unit){with_tactic (rw_and_try proof) (squash req)})
        : Tot (x:a{req /\ ens x}) =
            // GM: need to explicitly bring this (squash req) into the
            // logical environment. Unsure why the SMT pattern doesn't
            // kick in
            by_tactic_seman unit (rw_and_try proof) (squash req);
            f ()
        //this is weird, but the sequencing "encourages" the
        //normalizer to actually reduce f(), which is important below
        //(see XXX)
#reset-options

let tcalc = ignore
let using x = fun () -> x
let z3 = ()
let done = ()
let qed = ()
(* let ( &. ) (#a : Type) (x:a) (_:unit) = () *)
