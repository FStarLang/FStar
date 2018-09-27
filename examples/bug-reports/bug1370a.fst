module Bug1370a

open FStar.Pervasives
open FStar.Exn

// inferred type: Raises : ex:Prims.exn -> a:Type0 -> Prims.Tot Effect
effect Raises (a:Type) (ex:exn) =
    Exn a (requires True)
        (ensures (function
                | (V _) -> True
                | (E e) -> e == ex
                | _ -> False
        ))

exception Bad
exception ReallyBad

val u : nat -> Raises nat Bad
let u i = if i > 10
    then i
    else raise Bad                  // expected to work

val u' : nat -> Raises nat Bad

[@expect_failure]
let u' i = if i > 10
    then i
    else raise ReallyBad         // expected to fail type checking
