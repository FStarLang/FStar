module FStar.PropositionalExtensionality

open FStar.Constructive

assume val propositionalExtensionalityConstr :
  p:Type -> q:Type -> h:(ciff p q) -> Tot (ceq_type p q)

assume val propositionalExtensionality :
  p:Type -> q:Type -> Pure unit (requires (p <==> q))
                                (ensures (fun _ -> (p == q)))
(* apparently SMT solver can't prove it at the moment
let propositionalExtensionality (p:Type) (q:Type) = ()
 *)
