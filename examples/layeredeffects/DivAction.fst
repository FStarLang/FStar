module DivAction

(* This example used to define a layered identity/divergence effect.  The
   effect has been replaced by its underlying monad, unit -> Dv a. *)

let repr (a : Type) : Type = unit -> Dv a

let return (a : Type) (x : a) : repr a =
  fun () -> x

let bind (a b : Type) (v : repr a) (f : (a -> repr b)) : repr b  =
  fun () -> f (v ()) ()

let (let!) (#a #b : Type) (v : repr a) (f : a -> repr b) : repr b =
  bind a b v f

val fix : #a:_ -> #b:_ -> ((a -> repr b) -> (a -> repr b)) -> (a -> repr b)
let fix #a #b f =
  let rec fixed : (a -> Dv b) =
    fun x -> f (fun y () -> fixed y) x ()
  in
  fun x () -> fixed x

[@@expect_failure]
let rec bad_div (x:int) : repr int = bad_div x

let good_div : int -> repr int = fix #int #int (fun f x -> f x)

let test (x:int) : Dv int = good_div x ()
