(*--build-config
    other-files: constr.fst;
  --*)
module Russell

open FStar.Constructive

(* Russell's paradox; didn't expect this to work, but it does ... even if
   - we don't have Type : Type -- or so I thought *)

(* The proof follows the one from The Essence of Coq as a Formal System
   by Bart Jacobs (http://people.cs.kuleuven.be/~bart.jacobs/coq-essence.pdf)
   which in turn is based on a proof by Paolo Capriotti. *)

type U = | Set : i:Type  -> p:(i -> Type) -> f:(i -> Tot U) -> U

type in_set (x:U) (y:U) =
  cexists #(Set.i y) (fun (ii:Set.i y) -> cand (Set.p y ii) (ceq #U (Set.f y ii) x))

val id : U -> Tot U
let id x = x

(* The definition of spec fails in Coq because of a universe inconsistency *)
val spec : (U -> Type) -> Tot U
let spec (p:(U->Type)) = Set U p id

val spec_intro : p:(U->Type) -> x:U -> h:(p x) -> Tot (in_set x (spec p))
let spec_intro (p:U->Type) (x:U) (h:(p x)) = ExIntro x (Conj h (Refl (id x)))

val spec_elim : p:(U->Type) -> x:U -> h:(in_set x (spec p)) -> Tot (p x)
let spec_elim (p:U->Type) (x:U) h =
  let ExIntro i (Conj h1 h2) = h in h1

type pr (x:U) = cnot (in_set x x)

val contradiction : p:Type -> h1:(cnot p -> Tot       p ) ->
                              h2:(     p -> Tot (cnot p)) -> Tot cfalse
let contradiction (p:Type) h1 h2 =
  (fun (h3:(cnot p)) -> h3 (h1 h3)) (fun (hp:p) -> h2 hp hp)

val absurd : unit -> Tot cfalse
let absurd () = contradiction (in_set (spec pr) (spec pr))
                              (spec_intro pr (spec pr))
                              (spec_elim  pr (spec pr))
