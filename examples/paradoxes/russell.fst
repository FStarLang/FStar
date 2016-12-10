module Russell
open FStar.Constructive

(* Russell's paradox *)

(* this file relies on a violation of the cardinality constraints of Type*)
#set-options "--cardinality warn"

(* The proof follows the one from The Essence of Coq as a Formal System
   by Bart Jacobs (http://people.cs.kuleuven.be/~bart.jacobs/coq-essence.pdf)
   which in turn is based on a proof by Paolo Capriotti. *)

noeq type u_type : Type u#(1 + max 'ua 'ub)= | Set : i:Type 'ua  -> p:(i -> Type 'ub) -> f:(i -> Tot u_type) -> u_type

type in_set (x:u_type) (y:u_type) =
  cexists (fun (ii:Set?.i y) -> cand (Set?.p y ii) (ceq (Set?.f y ii) x))

val id : u_type -> Tot u_type
let id x = x

(* The definition of spec fails in Coq because of a universe inconsistency *)
val spec : (u_type -> Type) -> Tot u_type
let spec (p:(u_type->Type)) = Set u_type p id

val spec_intro : p:(u_type->Type) -> x:u_type -> h:(p x) -> Tot (in_set x (spec p))
let spec_intro (p:u_type->Type) (x:u_type) (h:(p x)) = ExIntro x (Conj h Refl)

val spec_elim : p:(u_type->Type) -> x:u_type -> h:(in_set x (spec p)) -> Tot (p x)
let spec_elim (p:u_type->Type) (x:u_type) h =
  let ExIntro i (Conj h1 h2) = h in h1

type pr (x:u_type) = cnot (in_set x x)

val contradiction : p:Type -> h1:(cnot p -> Tot       p ) ->
                              h2:(     p -> Tot (cnot p)) -> Tot cfalse
let contradiction (p:Type) h1 h2 =
  (fun (h3:(cnot p)) -> h3 (h1 h3)) (fun (hp:p) -> h2 hp hp)

val absurd : unit -> Tot cfalse
let absurd () =
  let r = spec pr in
  contradiction (in_set r r)
                (spec_intro pr r)
                (spec_elim  pr r)
