module Continuations

let repr (a:Type) = (a -> Type) -> Type

let return (a:Type) (x:a) = fun k -> k x

let bind (a : Type) (b : Type)
    (l : repr a) (f : a -> repr b) =
    fun k -> l (fun x -> f x k)

(* interpretation as pure wp *)
let interp (a:Type) (l : repr a) : pure_wp a = fun p -> l p

total
reifiable
reflectable
new_effect {
  CONT : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = pure_wp
     ; return_wp = pure_return
     ; bind_wp   = pure_bind_wp

     ; interp    = interp

     (* ; choose    = choose *)
}

let test1 () : CONT int (fun p -> p 5 /\ p 3) = 5
let test2 () : CONT int (fun p -> p 5 /\ p 3) = 3

// Whoa! This used to succeed since the effect is marked as reifiable,
// and Rel compares the representation types on each side for the
// subtyping. and both are just `unit -> list a`. I changed it to check
// the WPs via stronger-than instead of always unfolding.
[@expect_failure]
let test3 () : CONT int (fun p -> p 5 /\ p 3) = 4

effect Cont (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        CONT a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect ContTot (a:Type) = CONT a (pure_null_wp a)

#set-options "--debug Continuations --debug_level SMTQuery"

let __em (#a:Type) : repr (c_or a (a -> Type)) =
  fun (d : c_or a (a -> Type) -> Type) ->
    let devil (x:a) : Type = d (Left x) in
    d (Right devil)

assume val em : (#a:Type) -> CONT (c_or a (a -> Type)) (fun p -> forall x. p x)
// fails to typechecke due to universes..
//let em #a = CONT?.reflect (__em #a)

[@expect_failure]
let _ = assert False
