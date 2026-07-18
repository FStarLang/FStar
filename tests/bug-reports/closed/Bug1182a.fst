module Bug1182a

type func = nat -> Tot nat

val id1 (f:func) : func
let id1 f = fun n -> f n

let rec id2 f = fun n -> f n

val id3 (f:func) : func
let rec id3 f = fun n -> f n
(* Error: From its type f:FunctionAlias.func -> Prims.Tot FunctionAlias.func,
the definition of `let rec id3` expects a function with 1 argument, but 2
arguments were found *)
