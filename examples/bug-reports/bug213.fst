module Bug213

type intPair =
  | IP : f:int -> intPair

noeq type cexists (a:Type) (p:a -> Type) : Type =
  | ExIntro : x:a -> p x -> cexists a p

val foo : cexists intPair (fun (p:intPair) -> unit) -> Tot unit
let foo h =
  let ExIntro (IP p) hp = h in
  ()


noeq type cexists' : (a:Type) -> (p:a -> Type) -> Type =
  | ExIntro' : #a:Type -> #p:(a -> Type) -> x:a -> p x -> cexists' a p
val foo' : cexists' intPair (fun (p:intPair) -> unit) -> Tot unit
[@expect_failure 114]
let foo' h =
  let ExIntro' (IP p) hp = h in
  ()
