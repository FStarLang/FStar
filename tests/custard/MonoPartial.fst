module MonoPartial
open FStar.All
open FStar.IO
open FStar.Attributes

(* Section 3.2(a): [g] is passed as a function value, so its monomorphized
   binder is never supplied at a call site. *)
let g ([@@@monomorphize] n:nat) : nat = n + 1

let twice (f:nat -> nat) (x:nat) : nat = f (f x)

let main () : ML unit = print_string (string_of_int (twice g 3))
