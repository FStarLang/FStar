module Raising

(* Taken from #1370, due to Wolfram Kahl *)

open FStar.Pervasives
open FStar.Exn

effect Raises (a:Type) (ex:exn) =
    Exn a (requires True)
        (ensures (function
                | V _ -> True
                | E e -> e == ex
                | _ -> False
        ))

exception Bad

val u : nat -> Raises nat Bad
let u i = if i > 10
    then i
    else raise Bad
