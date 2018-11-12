module Bug1141b

effect MyTot (a:Type) = PURE a (fun p -> forall x. p x)

[@expect_failure]
noeq
type np (a : Type) = | Mk : (np a -> MyTot a) -> np a

(* This is how to prove false out of that type, were it to succeed *)
(*
let self #a (v : np a) : a =
    match v with
    | Mk f -> f v

let loop #a (f : a -> a) : a =
    self (Mk (fun x -> f (self x)))

val falso : squash False
let falso = loop (fun x -> x)
*)
