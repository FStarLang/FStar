module CoerceLamRes

(* A record of lambdas whose result type is [id int]: the expected result is
   [m int] at [m := any], so each body is coerced to [any], and the lambda has
   to take the result type of its coerced body.  Left at [int], it was coerced
   as a whole too, and Cherry took [int] out of the [any]. *)

open FStar.All

type id (a:Type0) = a

noeq type vis (m:Type0 -> Type0) = {
  f_int : int -> ML (m int);
  f_bool : bool -> ML (m bool);
}

let run (#m:Type0 -> Type0) (d:vis m) (x:int) : ML (m int) = d.f_int x

let tie (k:int) : ML (vis id) =
  let r : ref int = alloc k in
  let d : vis id = {
    f_int = (fun (x:int) -> let e = !r in (x + e <: id int));
    f_bool = (fun (b:bool) -> (not b <: id bool)) } in
  d

let main () : ML unit =
  let d = tie 1 in
  let n : int = run (FStar.Custard.dyn d) 41 in
  FStar.IO.print_string (string_of_int n ^ "\n")
