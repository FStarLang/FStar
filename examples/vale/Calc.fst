module Calc

open FStar.Tactics
open FStar.Tactics.Canon

//The normalize_term's here are important, see (XXX)
let ( &= ) (#a:Type) (x:a) (y:a) : 
    (unit -> Pure a (requires (normalize_term x == y)) (fun z -> z == y /\  
							 normalize_term x == y))
  = fun () -> y

(** Combinator used to discharge equalities with SMT/lemmas*)
let ( &| ) #a #req (#ens : a -> Type0) ($f:(unit -> Pure a req ens)) (proof:unit -> Lemma req)
    : Tot (x:a{ens x})
  = proof (); f ()

(* Now that we have ranges inside of tactic definitions, we need to abstract
 * this away so F* doesn't need to prove a range equality (which it can't)
 * to typecheck (&||). *)
private let rw_and_try (proof : tactic unit) : tactic unit =
    rewrite_eqs_from_context;;
    norm[delta];;
    proof

#reset-options "--no_tactics"
(** Combinator used to discharge equalities with tactics*)
let ( &|| ) #a #req #ens ($f:(unit -> Pure a req ens))
      (proof: tactic unit{by_tactic  
	(rw_and_try proof) (squash req)})
	: Tot (x:a{ens x}) = (); f ()  
	//this is weird, but the sequencing "encourages" the
	//normalizer to actually reduce f(), which is important below
	//(see XXX)
#reset-options

let calc = ignore 
let using x = fun () -> x
let z3 = ()
let done = ()
let qed = ()
(* let ( &. ) (#a : Type) (x:a) (_:unit) = () *)
