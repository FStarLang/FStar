module PartialityTotal

(* Reasoning about partial programs with
 * pure WPs, in a total correctness setting. That is,
 * a partial program has a false precondition. *)

let repr (a:Type) = option a

let return (a:Type) (x:a) = Some x

let bind (a : Type) (b : Type) (l : repr a) (f : a -> repr b) =
  match l with
  | Some x -> f x
  | None -> None

let interp (#a:Type) (l : repr a) : pure_wp a =
    fun p -> match l with | Some x -> p x | _ -> False

total
reifiable
reflectable
new_effect {
  DIV : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = pure_wp
     ; return_wp = pure_return
     ; bind_wp   = pure_bind_wp

     ; interp    = interp
}

let omega (#a:Type) () : DIV a (fun p -> False)  =
  DIV?.reflect None

(* An alias for convenience *)
effect Dv (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        DIV a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

let test (x:int) : DIV int (fun p -> x >= 0 /\ (forall y. p y)) =
  if x < 0 then
    omega ();
  x + x

let test' (x:int) : Dv int (requires (x >= 0)) (ensures (fun _ -> True)) =
  if x < 0 then
    omega ();
  x + x

(* This is an expected failure, since x could be negative, and this
 * program should not verify with a trivial precondition. *)
[@expect_failure]
let test'' (x:int) : Dv int (requires True) (ensures (fun _ -> True)) =
  if x < 0 then
    omega ();
  x + x
