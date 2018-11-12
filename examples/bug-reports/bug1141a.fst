module Bug1141a

let id (a:Type) = unit -> M a

val return_id : (a:Type) -> (x:a) -> id a
let return_id a x = fun _ -> x

val bind_id : (a:Type) -> (b:Type) -> (f:id a) -> (g:a -> id b) -> id b
let bind_id a b f g = fun _ ->
  let r = f () in g r ()

total reifiable reflectable new_effect {
  IDN : (a:Type) -> Effect
  with repr     = id
     ; bind     = bind_id
     ; return   = return_id
}

effect ID (a:Type) = IDN a (fun () p -> forall x. p x)

[@expect_failure]
noeq
type np (a : Type) =
    | Mk : (np a -> ID a) -> np a

(* This is how to prove false out of that type, were it to succeed *)
(*
val self : (#a:Type) -> np a -> ID a
let self #a v =
    match v with
    | Mk f -> f v

val loop : (#a:Type) -> (a -> a) -> a
let loop #a f = reify (self (Mk (fun x -> f (self x)))) ()

val falso : squash False
let falso = loop (fun x -> x)
*)
