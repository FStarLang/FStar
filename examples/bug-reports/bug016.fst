module Bug016

open FStar.All

val impossible : u : unit { False } -> Tot 'a
let impossible = failwith "this won't happen"

val id : 'a -> 'a
let id x = x
let three = id 3

