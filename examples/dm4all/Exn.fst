module Exn

(* Reasoning about programs with exceptions, but with
 * pure WPs, in a total correctness setting. That is,
 * raising an exception has a false precondition. *)

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

let raise (#a:Type) (e:exn) : EXN a (fun p -> False)  =
  EXN?.reflect (Inr e)

(* An alias for convenience *)
effect Ex (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        EXN a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))
exception Neg

let test (x:int) : EXN int (fun p -> x >= 0 /\ (forall y. p y)) =
  if x < 0 then
    raise Neg;
  x + x

let test' (x:int) : Ex int (requires (x >= 0)) (ensures (fun _ -> True)) =
  if x < 0 then
    raise Neg;
  x + x

(* This is an expected failure, since x could be negative, and this
 * program should not verify with a trivial precondition. *)
[@expect_failure]
let test'' (x:int) : Ex int (requires True) (ensures (fun _ -> True)) =
  if x < 0 then
    raise Neg;
  x + x
