module StringEncodings

#push-options "--smtencoding.encode_string true"

open FStar.String

let hello = "hello"
let world = "world"
let helloworld = strcat "hello" "world"

val length_hello: unit -> Lemma (strlen hello = 5)
let length_hello () = ()

val length_hello_2: unit -> Lemma (length hello = 5)
let length_hello_2 () = ()

val helloworld_literal: unit -> Lemma (helloworld = "helloworld")
let helloworld_literal () = ()

val str_substr: unit -> Lemma (sub helloworld 1 2 = "el")
let str_substr () = ()

(*
FIXME: The following lemmas can't be verified yet.
Z3 4.8.5 doesn't have str.to_code and str.from_code for conversion between
singleton strings and character codes.
Using later versions of Z3, need to investigate why the verification conditions
result in unknown results.
*)

(*
val str_index_of_present: unit -> Lemma (index_of helloworld 'w' = 5)
let str_index_of_present () = ()

val str_index_of_absent: unit -> Lemma (index_of helloworld 'x' = -1)
let str_index_of_absent () = ()

val str_at: unit -> Lemma (index helloworld 5 = 'w')
let str_at () = ()
*)
