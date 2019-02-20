module Cont2

let repr (ans:Type) (a:Type) = (a -> ans) -> ans

let return (ans:Type) (a:Type) (x:a) = fun k -> k x

let bind (ans:Type) (a : Type) (b : Type)
    (l : repr ans a) (f : a -> repr ans b) =
    fun k -> l (fun x -> f x k)

let wpty ans a = (a -> pure_wp ans) -> pure_wp ans

assume val x : ans:_ -> pure_wp ans

//let interp (ans:Type) (a:Type) (l : repr ans a) : wpty ans a =

let interp (ans:Type) (a:Type) (l : (a -> ans) -> ans) : (a -> pure_wp ans) -> pure_wp ans =
  fun (kwp : a -> (ans -> Type) -> Type) (post : ans -> Type) -> post (l (fun (x:a) -> kwp x post))

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


let callcc #a #b (f : a -> Type)


[@expect_failure]
let _ = assert False
