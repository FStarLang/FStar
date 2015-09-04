(*--build-config
    other-files:constr.fst
  --*)
module Berardi

open FStar.Constructive

(* Berardi's paradox:
   https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Berardi.html
   This was brought to our attention by Maxime Denes.
*)

(* Ingredient #1: impredicative polymorphism in Type *)

type t = a:Type -> Tot a
val foo : t -> Tot t
let foo f = f t

(* Ingredient #2: excluded middle in Type *)

assume val excluded_middle_constr : a:Type -> Tot (cor a (cnot a))

(* #1 + #2 imply proof/term irrelevance in Type
  (so this assume should go away) *)

assume val proof_irrelevance : #a:Type -> x:a -> y:a -> Tot (ceq x y)

val false_elim : u:unit{false} -> Tot 'a
let false_elim () = ()

(* Proof irrelevance in Type implies False *)

val contradiction : unit -> Tot cfalse
let contradiction () = false_elim (ceq_eq (proof_irrelevance true false))


(* Another place where this could happen is in the refinement logic *)

(* the SMT solver can of course prove excluded middle
   (here had to pass silly unit argument) *)
val excluded_middle_ref : p:Type -> unit -> Lemma (p \/ ~p)
let excluded_middle_ref () = ()

(* we would then need to trick the SMT solver to prove Berardi's paradox;
   given that it also has foralls it doesn't seem impossible that this might work *)

assume val proof_irrelevance_ref : #a:Type -> x:a -> y:a -> Lemma (x = y)

val contradiction_ref : unit -> Lemma false
let contradiction_ref () = proof_irrelevance_ref true false

assume val get_proof: a:Type -> Ghost a (requires a) (ensures (fun _ -> True))


(* Some more work on this with Maxime on Sept 3, 2015 *)

val excluded_middle'' : p:Type -> GTot (p \/~p)
let excluded_middle'' (p:Type) = get_proof (p\/~p)

type pow (p:Type) = p -> Tot bool

type U = p:Type -> Tot (pow p)

val f : U -> Tot (pow U)
let f u = u U

assume val g : pow U -> Tot U

val r : U
let r = g (fun (u:U) -> op_Negation (u U u))

assume val not_has_fixpoint : ceq (r U r) (op_Negation (r U r))
// wip
