module StrCat

#push-options "--smtencoding.encode_string true"

open FStar.String

let hello = "hello"
let world = "world"
let helloworld = strcat "hello" "world"

val length_hello: unit -> Lemma (strlen hello = 5)
let length_hello () = ()

val helloworld_literal: unit -> Lemma (helloworld = "helloworld")
let helloworld_literal () = ()
