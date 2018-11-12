module NTP

assume val foo : x : int{x > 0} -> Tot bool

val u : x:int{x>0}
let u =
  match 42 with
  | x when foo x -> 45

(*
Term has an unexpected non-trivial pre-condition:
[Before:((fun a:Type wp:(_:(_:a => Type) => Type) => (wp (fun x:a => True))) bool (fun p:(_:bool => Type) => (l_and (Meta (labeled "This term may not terminate (non-trivial-precondition.fst(8,15-8,16))") (l_and (Meta (labeled "Subtyping check failed; expected type [Before:x:int{(b2t (op_GreaterThan x 0))}][After:x:int{(b2t (op_GreaterThan x 0))}]; got type [Before:int][After:int] (non-trivial-precondition.fst(8,15-8,16))") (b2t (op_GreaterThan x 0))) True)) (Forall #bool (fun x:bool => (p x))))))]
[After:(b2t (op_GreaterThan x 0)) /\ True /\ (forall x:bool. True)]
*)
