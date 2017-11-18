module Bug213

type intPair =
  | IP : intPair

noeq type cexists : a:Type0 -> (a -> Type0) -> Type u#1 =
  | ExIntro : #a:Type0 -> #p:(a -> Type0) -> x:a -> p x -> cexists a p

val foo : cexists intPair (fun (p:intPair) -> unit) -> Tot unit
let foo h =
  let ExIntro IP hp = h in
  ()
