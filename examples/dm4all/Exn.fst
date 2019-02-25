module Exn

module List = FStar.List.Tot

let repr (a:Type) = either a exn

let return (a:Type) (x:a) = Inl x

let bind (a : Type) (b : Type) (l : repr a) (f : a -> repr b) =
  match l with
  | Inl x -> f x
  | Inr e -> Inr e

let interp (#a:Type) (l : repr a) : pure_wp a =
    fun p -> match l with | Inl x -> p x | _ -> False

total
reifiable
reflectable
new_effect {
  EXN : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = pure_wp
     ; return_wp = pure_return
     ; bind_wp   = pure_bind_wp

     ; interp    = interp
}

let test1 () : EXN int (fun p -> p 5 /\ p 3) = 5
let test2 () : EXN int (fun p -> p 5 /\ p 3) = 3
[@expect_failure]
let test3 () : EXN int (fun p -> p 5 /\ p 3) = 4

effect Ex (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        EXN a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect ExTot (a:Type) = EXN a (pure_null_wp a)

(* GM: Why is this forcing me to Type0? *)
val raise : #a:Type0 -> e:exn -> EXN a (fun p -> False)
let raise #a e = EXN?.reflect (Inr e)

exception Neg

let test (x:int) : EXN int (fun p -> x >= 0 /\ (forall y. p y)) =
  if x < 0 then
    raise Neg;
  x + x
  
let test' (x:int) : Ex int (requires (x >= 0)) (ensures (fun _ -> True)) =
  if x < 0 then
    raise Neg;
  x + x

[@expect_failure]
let test'' (x:int) : Ex int (requires True) (ensures (fun _ -> True)) =
  if x < 0 then
    raise Neg;
  x + x

[@expect_failure]
let _ = assert False
